# The note proofs for PROOF.bend (imported by pgen2.py): a note read back
# from its bytes, and a list of notes. Each step is a rewrite whose motive is
# the whole goal, too long to write by hand, so the motives are built here.
#
# The bytes of a note are seven pieces: the three header words (LE), the name
# (NL), its padding (Z1), the descriptor (DL) and its padding (Z2). The proof
#   1. flattens to_list(write(n) ++ rest) into the pieces, by bytes' laws
#      octets_append_list and octets_zeros_list (note_bytes);
#   2. reads the header on symbolic bits (note_hdr_bits), then the name and
#      descriptor by the hypotheses that their lengths are the sizes
#      (note_body);
#   3. for a list, walks the bytes a note takes (its length is 1 + the size
#      the reader computes, note_len) to the next note (note_step).

L = "List<&2, U32>"
RL = "Result<&2, &2, F.ElfError, List<&2, U32>>"
RN = "Result<&2, &2, F.ElfError, N.ElfNoteRead>"
RLN = "Result<&2, &2, F.ElfError, List<&2, N.ElfNote>>"


def app(a, b):
    return "B.append(%s, %s)" % (a, b)


def nest(ps, last=None):
    """p1 ++ (p2 ++ (... ++ pn)), or ... ++ (pn ++ last)"""
    ps = list(ps)
    s = ps[-1] if last is None else app(ps[-1], last)
    for p in reversed(ps[:-1]):
        s = app(p, s)
    return s


def LE(v):
    return "B.Octets.to_list(F.elf_w32(big, %s))" % v


P1 = "N.elf_note.pad(al, U32.add(12, nz))"
P2 = "N.elf_note.pad(al, dz)"
Z1 = "B.zeros(%s)" % P1
Z2 = "B.zeros(%s)" % P2


def pieces(NL, DL):
    return [LE("nz"), LE("dz"), LE("t"), NL, Z1, DL, Z2]


def flatw(NL, DL):
    return nest(pieces(NL, DL))


def flat(NL, DL, R):
    return nest(pieces(NL, DL), R)


SIZE = "N.elf_note.size(al, nz, dz)"
NOTE = "N.ElfNote{nz, dz, t, name, desc}"
W = "N.ElfNote.write(big, al, %s)" % NOTE
NL0, DL0 = "B.Octets.to_list(name)", "B.Octets.to_list(desc)"


def read(NL, DL):
    return "Done{N.ElfNoteRead{N.ElfNote{nz, dz, t, B.Octets.of_list(%s), B.Octets.of_list(%s)}, %s}}" % (NL, DL, SIZE)


def wrap(ctx, hole):
    """ctx: a motive with one '@' where the hole goes"""
    return ctx.replace("@", hole)


def gen():
    out = []
    ps7 = ["p%d" % i for i in range(1, 8)]
    PS7 = ", ".join("+%s: %s" % (p, L) for p in ps7)
    out.append("""# Notes (notes.bend). %s
""" % "The note proofs are written by gen/pnotes.py.")
    out.append(f"""def note_assoc(+x: {L}, +y: {L}, +z: {L}) -> {{{app(app("x", "y"), "z")} == {app("x", app("y", "z"))} : {L}}}:
  match x:
    case Nil{{}}:
      {{==}}
    case Con{{+h, +t}}:
      %note_assoc(t, y, z) : {{Con{{h, {app(app("t", "y"), "z")}}} == Con{{h, _}} : {L}}}
      {{==}}

def note_al(+a: {L}, +r: {L}) -> {{True{{}} == F.elf_at_least(B.len(a), {app("a", "r")}) : Bool}}:
  match a:
    case Nil{{}}:
      {{==}}
    case Con{{+h, +t}}:
      note_al(t, r)

def note_take_app(+a: {L}, +r: {L}) -> {{a == B.take(B.len(a), {app("a", "r")}) : {L}}}:
  match a:
    case Nil{{}}:
      {{==}}
    case Con{{+h, +t}}:
      %note_take_app(t, r) : {{Con{{h, t}} == Con{{h, _}} : {L}}}
      {{==}}

def note_cut(+a: {L}, +r: {L}) -> {{N.elf_note.cut(B.len(a), {app("a", "r")}) == Done{{a}} : {RL}}}:
  %note_al(a, r) : {{N.elf_note.cut.go(_, B.len(a), {app("a", "r")}) == Done{{a}} : {RL}}}
  %BL.take_fast(B.len(a), {app("a", "r")}) : {{Done{{_}} == Done{{a}} : {RL}}}
  %note_take_app(a, r) : {{Done{{_}} == Done{{a}} : {RL}}}
  {{==}}

def note_drop_app(+a: {L}, +r: {L}) -> {{r == B.drop(B.len(a), {app("a", "r")}) : {L}}}:
  match a:
    case Nil{{}}:
      {{==}}
    case Con{{+h, +t}}:
      note_drop_app(t, r)

def note_drop_zeros(+n: Nat, +r: {L}) -> {{r == B.drop(n, {app("B.zeros(n)", "r")}) : {L}}}:
  match n:
    case 0n:
      {{==}}
    case 1n+(+p):
      note_drop_zeros(p, r)

def note_len_app(+a: {L}, +b: {L}) -> {{B.len({app("a", "b")}) == Nat.add(B.len(a), B.len(b)) : Nat}}:
  match a:
    case Nil{{}}:
      {{==}}
    case Con{{+h, +t}}:
      %note_len_app(t, b) : {{1n+B.len({app("t", "b")}) == 1n+_ : Nat}}
      {{==}}

def note_len_zeros(+n: Nat) -> {{n == B.len(B.zeros(n)) : Nat}}:
  match n:
    case 0n:
      {{==}}
    case 1n+(+p):
      %note_len_zeros(p) : {{1n+p == 1n+_ : Nat}}
      {{==}}
""")
    # seven pieces: reassociated, and their length
    cur = app(nest(ps7), "R")
    final = nest(ps7, "R")
    s = f"def note_flat7({PS7}, +R: {L}) -> {{{cur} == {final} : {L}}}:\n"
    ctx = "@"
    for i in range(6):
        y = nest(ps7[i + 1:])
        a_, b_ = app(ps7[i], app(y, "R")), app(app(ps7[i], y), "R")
        s += f"  %Equal.sym({L}, {b_}, {a_}, note_assoc({ps7[i]}, {y}, R)) : {{{wrap(ctx, '_')} == {final} : {L}}}\n"
        ctx = wrap(ctx, app(ps7[i], "@"))
    s += "  {==}\n"
    out.append(s)
    lens = ["B.len(%s)" % p for p in ps7]
    def nadd(xs):
        s_ = xs[-1]
        for x in reversed(xs[:-1]):
            s_ = "Nat.add(%s, %s)" % (x, s_)
        return s_
    SUM7 = nadd(lens)
    s = f"def note_len7({PS7}) -> {{B.len({nest(ps7)}) == {SUM7} : Nat}}:\n"
    ctx = "@"
    for i in range(6):
        y = nest(ps7[i + 1:])
        s += f"  %Equal.sym(Nat, B.len({app(ps7[i], y)}), Nat.add(B.len({ps7[i]}), B.len({y})), note_len_app({ps7[i]}, {y})) : {{{wrap(ctx, '_')} == {SUM7} : Nat}}\n"
        ctx = wrap(ctx, "Nat.add(B.len(%s), @)" % ps7[i])
    s += "  {==}\n"
    out.append(s)

    # a header word is 4 bytes, on symbolic bits
    def u32(p):
        b = "WNil{}"
        for i in reversed(range(32)):
            b = "WCon{%s%d, %s}" % (p, i, b)
        return "U32{%s}" % b
    s = f"def note_len4(big: Bool, v: U32) -> {{4n == B.len({LE('v')}) : Nat}}:\n  match big v:\n"
    for bb in ["True{}", "False{}"]:
        s += "    case %s %s:\n      {==}\n" % (bb, u32("v_"))
    out.append(s)
    # the header read on symbolic bits
    HB = f"{{N.ElfNote.parse.list(big, al, {nest([LE('nz'), LE('dz'), LE('t')], 'ys')}) == N.elf_note.body(al, nz, dz, t, ys) : {RN}}}"
    s = f"def note_hdr_bits(big: Bool, nz: U32, dz: U32, t: U32, +al: N.ElfNoteAlign, +ys: {L}) -> {HB}:\n  match big nz dz t:\n"
    for bb in ["True{}", "False{}"]:
        s += "    case %s %s %s %s:\n      {==}\n" % (bb, u32("nz_"), u32("dz_"), u32("t_"))
    out.append(s)

    # the name and descriptor, by the hypotheses
    YS = nest(["NL", Z1, "DL", Z2], "r")
    R1 = nest([Z1, "DL", Z2], "r")
    R2 = nest(["DL", Z2], "r")
    R3 = app(Z2, "r")
    RHSB = read("NL", "DL")
    E1 = "e1: {B.len(NL) == U32.to_nat(nz) : Nat}"
    E2 = "e2: {B.len(DL) == U32.to_nat(dz) : Nat}"
    out.append(f"""def note_body(+al: N.ElfNoteAlign, +nz: U32, +dz: U32, +t: U32, +NL: {L}, +DL: {L}, +r: {L}, {E1}, {E2}) -> {{N.elf_note.body(al, nz, dz, t, {YS}) == {RHSB} : {RN}}}:
  %e1 : {{N.elf_note.body2(N.elf_note.cut(_, {YS}), al, nz, dz, t, B.drop({P1}, B.drop(_, {YS}))) == {RHSB} : {RN}}}
  %Equal.sym({RL}, N.elf_note.cut(B.len(NL), {app("NL", R1)}), Done{{NL}}, note_cut(NL, {R1})) : {{N.elf_note.body2(_, al, nz, dz, t, B.drop({P1}, B.drop(B.len(NL), {YS}))) == {RHSB} : {RN}}}
  %note_drop_app(NL, {R1}) : {{N.elf_note.body2(Done{{NL}}, al, nz, dz, t, B.drop({P1}, _)) == {RHSB} : {RN}}}
  %note_drop_zeros({P1}, {R2}) : {{N.elf_note.body2(Done{{NL}}, al, nz, dz, t, _) == {RHSB} : {RN}}}
  %e2 : {{N.elf_note.body3(N.elf_note.cut(_, {R2}), al, nz, dz, t, NL) == {RHSB} : {RN}}}
  %Equal.sym({RL}, N.elf_note.cut(B.len(DL), {app("DL", R3)}), Done{{DL}}, note_cut(DL, {R3})) : {{N.elf_note.body3(_, al, nz, dz, t, NL) == {RHSB} : {RN}}}
  {{==}}

# a note's bytes followed by any bytes R
def note_parse(+big: Bool, +al: N.ElfNoteAlign, +nz: U32, +dz: U32, +t: U32, +NL: {L}, +DL: {L}, +R: {L}, {E1}, {E2}) -> {{N.ElfNote.parse.list(big, al, {app(flatw("NL", "DL"), "R")}) == {RHSB} : {RN}}}:
  %Equal.sym({L}, {app(flatw("NL", "DL"), "R")}, {flat("NL", "DL", "R")}, note_flat7({", ".join(pieces("NL", "DL"))}, R)) : {{N.ElfNote.parse.list(big, al, _) == {RHSB} : {RN}}}
  Equal.trans({RN}, N.ElfNote.parse.list(big, al, {flat("NL", "DL", "R")}), N.elf_note.body(al, nz, dz, t, {nest(["NL", Z1, "DL", Z2], "R")}), {RHSB}, note_hdr_bits(big, nz, dz, t, al, {nest(["NL", Z1, "DL", Z2], "R")}), note_body(al, nz, dz, t, NL, DL, R, e1, e2))
""")
    # the bytes of a note, flattened
    OA = "B.Octets.append"
    oct_pieces = ["F.elf_w32(big, nz)", "F.elf_w32(big, dz)", "F.elf_w32(big, t)", "name", "B.Octets.zeros(%s)" % P1, "desc", "B.Octets.zeros(%s)" % P2]
    def onest(ps):
        s_ = ps[-1]
        for p in reversed(ps[:-1]):
            s_ = "%s(%s, %s)" % (OA, p, s_)
        return s_
    target = flatw(NL0, DL0)
    s = f"def note_bytes0(+big: Bool, +al: N.ElfNoteAlign, +nz: U32, +dz: U32, +t: U32, +name: B.Octets, +desc: B.Octets) -> {{B.Octets.to_list({W}) == {target} : {L}}}:\n"
    ctx = "@"
    for i in range(6):
        a_, rest_ = oct_pieces[i], onest(oct_pieces[i + 1:])
        whole = "%s(%s, %s)" % (OA, a_, rest_)
        s += f"  %Equal.sym({L}, B.Octets.to_list({whole}), {app('B.Octets.to_list(%s)' % a_, 'B.Octets.to_list(%s)' % rest_)}, BL.octets_append_list({a_}, {rest_})) : {{{wrap(ctx, '_')} == {target} : {L}}}\n"
        ctx = wrap(ctx, app("B.Octets.to_list(%s)" % a_, "@"))
    # now: the pieces as to_list(...) of each; the zeros are bytes' zeros lists
    full = nest(["B.Octets.to_list(%s)" % p for p in oct_pieces])
    z1, z2 = "B.Octets.to_list(B.Octets.zeros(%s))" % P1, "B.Octets.to_list(B.Octets.zeros(%s))" % P2
    m1 = full.replace(z1, "_")
    s += f"  %Equal.sym({L}, {z1}, {Z1}, BL.octets_zeros_list({P1})) : {{{m1} == {target} : {L}}}\n"
    full = full.replace(z1, Z1)
    m2 = full.replace(z2, "_")
    s += f"  %Equal.sym({L}, {z2}, {Z2}, BL.octets_zeros_list({P2})) : {{{m2} == {target} : {L}}}\n"
    s += "  {==}\n"
    out.append(s)

    # one note, with any bytes after it
    E1n = "e1: {B.Octets.len(name) == U32.to_nat(nz) : Nat}"
    E2n = "e2: {B.Octets.len(desc) == U32.to_nat(dz) : Nat}"
    e1l = f"Equal.trans(Nat, B.len({NL0}), B.Octets.len(name), U32.to_nat(nz), Equal.sym(Nat, B.Octets.len(name), B.len({NL0}), BL.octets_len_list(name)), e1)"
    e2l = f"Equal.trans(Nat, B.len({DL0}), B.Octets.len(desc), U32.to_nat(dz), Equal.sym(Nat, B.Octets.len(desc), B.len({DL0}), BL.octets_len_list(desc)), e2)"
    RN1 = "Result<&2, &2, F.ElfError, N.ElfNote>"
    out.append(f"""def note_rt(+big: Bool, +al: N.ElfNoteAlign, +nz: U32, +dz: U32, +t: U32, +name: B.Octets, +desc: B.Octets, +rest: B.Octets, {E1n}, {E2n}) -> {{N.ElfNote.parse(big, al, B.Octets.append({W}, rest)) == Done{{{NOTE}}} : {RN1}}}:
  %Equal.sym({L}, B.Octets.to_list(B.Octets.append({W}, rest)), {app("B.Octets.to_list(%s)" % W, "B.Octets.to_list(rest)")}, BL.octets_append_list({W}, rest)) : {{N.elf_note.only(N.ElfNote.parse.list(big, al, _)) == Done{{{NOTE}}} : {RN1}}}
  %Equal.sym({L}, B.Octets.to_list({W}), {flatw(NL0, DL0)}, note_bytes0(big, al, nz, dz, t, name, desc)) : {{N.elf_note.only(N.ElfNote.parse.list(big, al, {app("_", "B.Octets.to_list(rest)")})) == Done{{{NOTE}}} : {RN1}}}
  %Equal.sym({RN}, N.ElfNote.parse.list(big, al, {app(flatw(NL0, DL0), "B.Octets.to_list(rest)")}), {read(NL0, DL0)}, note_parse(big, al, nz, dz, t, {NL0}, {DL0}, B.Octets.to_list(rest), {e1l}, {e2l})) : {{N.elf_note.only(_) == Done{{{NOTE}}} : {RN1}}}
  %BL.octets_of_to(name) : {{Done{{N.ElfNote{{nz, dz, t, B.Octets.of_list({NL0}), B.Octets.of_list({DL0})}}}} == Done{{N.ElfNote{{nz, dz, t, _, desc}}}} : {RN1}}}
  %BL.octets_of_to(desc) : {{Done{{N.ElfNote{{nz, dz, t, B.Octets.of_list({NL0}), B.Octets.of_list({DL0})}}}} == Done{{N.ElfNote{{nz, dz, t, B.Octets.of_list({NL0}), _}}}} : {RN1}}}
  {{==}}

def Laws.note_round_trip(big, al, namesz, descsz, t, name, desc, rest, e1, e2):
  note_rt(big, al, namesz, descsz, t, name, desc, rest, e1, e2)
""")

    # a note's length
    LENS = [("Equal.sym(Nat, 4n, B.len(%s), note_len4(big, %s))" % (LE(v), v), "4n") for v in ["nz", "dz", "t"]]
    s = f"def note_sum(+big: Bool, +al: N.ElfNoteAlign, +nz: U32, +dz: U32, +t: U32, +NL: {L}, +DL: {L}, {E1}, {E2}) -> {{{nadd(['B.len(%s)' % p for p in pieces('NL', 'DL')])} == 1n+{SIZE} : Nat}}:\n"
    terms = ["B.len(%s)" % p for p in pieces("NL", "DL")]
    vals = ["4n", "4n", "4n", "U32.to_nat(nz)", P1, "U32.to_nat(dz)", P2]
    proofs = [
        "note_len4(big, nz)", "note_len4(big, dz)", "note_len4(big, t)",
        "Equal.sym(Nat, B.len(NL), U32.to_nat(nz), e1)",
        "note_len_zeros(%s)" % P1,
        "Equal.sym(Nat, B.len(DL), U32.to_nat(dz), e2)",
        "note_len_zeros(%s)" % P2,
    ]
    for i in range(7):
        motive = nadd(vals[:i] + ["_"] + terms[i + 1:])
        s += f"  %{proofs[i]} : {{{motive} == 1n+{SIZE} : Nat}}\n"
    s += "  {==}\n"
    out.append(s)
    out.append(f"""def note_len(+big: Bool, +al: N.ElfNoteAlign, +nz: U32, +dz: U32, +t: U32, +NL: {L}, +DL: {L}, {E1}, {E2}) -> {{B.len({flatw("NL", "DL")}) == 1n+{SIZE} : Nat}}:
  Equal.trans(Nat, B.len({flatw("NL", "DL")}), {nadd(['B.len(%s)' % p for p in pieces('NL', 'DL')])}, 1n+{SIZE}, note_len7({", ".join(pieces("NL", "DL"))}), note_sum(big, al, nz, dz, t, NL, DL, e1, e2))
""")

    # walking the bytes a note takes
    GO = "N.elf_note.go"
    out.append(f"""def note_skip(+a: {L}, +r: {L}, +big: Bool, +al: N.ElfNoteAlign, +acc: List<&2, N.ElfNote>) -> {{{GO}({app("a", "r")}, N.elf_note.next(B.len(a), big, al, {app("a", "r")}), big, al, acc) == {GO}(r, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, r)}}, big, al, acc) : {RLN}}}:
  match a:
    case Nil{{}}:
      {{==}}
    case Con{{+h, +t}}:
      note_skip(t, r, big, al, acc)

def note_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def note_succ_inj(+a: Nat, +b: Nat, e: {{1n+a == 1n+b : Nat}}) -> {{a == b : Nat}}:
  %e : {{a == note_pred(_) : Nat}}
  {{==}}

def note_nat_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def note_nat_absurd(+k: Nat, e: {{0n == 1n+k : Nat}}) -> Empty:
  %e : note_nat_disc(_)
  Unit{{}}

def note_step(+a: {L}, +r: {L}, +big: Bool, +al: N.ElfNoteAlign, +n: N.ElfNote, +k: Nat, +acc: List<&2, N.ElfNote>, e: {{B.len(a) == 1n+k : Nat}}) -> {{{GO}({app("a", "r")}, N.ElfNoteHere{{Done{{N.ElfNoteRead{{n, k}}}}}}, big, al, acc) == {GO}(r, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, r)}}, big, al, Con{{n, acc}}) : {RLN}}}:
  match a:
    case Nil{{}}:
      Empty.absurd({{{GO}({app("Nil{}", "r")}, N.ElfNoteHere{{Done{{N.ElfNoteRead{{n, k}}}}}}, big, al, acc) == {GO}(r, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, r)}}, big, al, Con{{n, acc}}) : {RLN}}}, note_nat_absurd(k, e))
    case Con{{+h, +t}}:
      %note_succ_inj(B.len(t), k, e) : {{{GO}({app("t", "r")}, N.elf_note.next(_, big, al, {app("t", "r")}), big, al, Con{{n, acc}}) == {GO}(r, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, r)}}, big, al, Con{{n, acc}}) : {RLN}}}
      note_skip(t, r, big, al, Con{{n, acc}})

# Bool.and and Nat.is_eq, when True

def note_and_l(+a: Bool, +b: Bool, e: {{Bool.and(a, b) == True{{}} : Bool}}) -> {{a == True{{}} : Bool}}:
  match a:
    case True{{}}:
      {{==}}
    case False{{}}:
      Empty.absurd({{False{{}} == True{{}} : Bool}}, bool_absurd(e))

def note_and_r(+a: Bool, +b: Bool, e: {{Bool.and(a, b) == True{{}} : Bool}}) -> {{b == True{{}} : Bool}}:
  match a:
    case True{{}}:
      e
    case False{{}}:
      Empty.absurd({{b == True{{}} : Bool}}, bool_absurd(e))

def note_nat_eq(+a: Nat, +b: Nat, e: {{Nat.is_eq(a, b) == True{{}} : Bool}}) -> {{a == b : Nat}}:
  match a b:
    case 0n 0n:
      {{==}}
    case 0n 1n+q:
      Empty.absurd({{0n == 1n+q : Nat}}, bool_absurd(e))
    case 1n+p 0n:
      Empty.absurd({{1n+p == 0n : Nat}}, bool_absurd(e))
    case 1n+(+p) 1n+(+q):
      %note_nat_eq(p, q, e) : {{1n+p == 1n+_ : Nat}}
      {{==}}

# The tail-recursive writer is the structural one (as for the tables)

def note_wgo(+big: Bool, +al: N.ElfNoteAlign, +xs: List<&2, N.ElfNote>, +rs: List<&2, N.ElfNote>) -> {{N.ElfNote.write_all.go(big, al, F.elf_rev_onto(N.ElfNote, xs, rs), B.Octets.empty()) == N.ElfNote.write_all.go(big, al, rs, N.ElfNote.write_all.ref(big, al, xs)) : B.Octets}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{x, t}}:
      note_wgo(big, al, t, Con{{x, rs}})

def note_write_eq(+big: Bool, +al: N.ElfNoteAlign, +xs: List<&2, N.ElfNote>) -> {{N.ElfNote.write_all.ref(big, al, xs) == N.ElfNote.write_all(big, al, xs) : B.Octets}}:
  Equal.sym(B.Octets, N.ElfNote.write_all(big, al, xs), N.ElfNote.write_all.ref(big, al, xs), note_wgo(big, al, xs, Nil{{}}))
""")
    # the list: every note read in turn
    XS = "B.Octets.to_list(N.ElfNote.write_all.ref(big, al, ns))"
    RR = "N.ElfNote.write_all.ref(big, al, r)"
    R = "B.Octets.to_list(%s)" % RR
    XSc = "B.Octets.to_list(B.Octets.append(%s, %s))" % (W, RR)
    GOAL_R = "Done{F.elf_rev_onto(N.ElfNote, Con{%s, acc}, r)}" % NOTE
    def g(lst, parsed):
        return f"{GO}({lst}, N.ElfNoteHere{{{parsed}}}, big, al, acc)"
    A1 = app("B.Octets.to_list(%s)" % W, R)
    A2 = app(flatw(NL0, DL0), R)
    SZ = "N.elf_note.size(al, nz, dz)"
    HERE1 = "N.ElfNoteHere{Done{N.ElfNoteRead{N.ElfNote{nz, dz, t, _, B.Octets.of_list(%s)}, %s}}}" % (DL0, SZ)
    HERE2 = "N.ElfNoteHere{Done{N.ElfNoteRead{N.ElfNote{nz, dz, t, name, _}, %s}}}" % SZ
    HERE3 = "N.ElfNoteHere{Done{N.ElfNoteRead{%s, %s}}}" % (NOTE, SZ)
    out.append(f"""def note_list(+big: Bool, +al: N.ElfNoteAlign, +ns: List<&2, N.ElfNote>, +acc: List<&2, N.ElfNote>, +e: {{N.ElfNote.all_sized(ns) == True{{}} : Bool}}) -> {{{GO}({XS}, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, {XS})}}, big, al, acc) == Done{{F.elf_rev_onto(N.ElfNote, acc, ns)}} : {RLN}}}:
  match ns:
    case Nil{{}}:
      {{==}}
    case Con{{N.ElfNote{{+nz, +dz, +t, +name, +desc}}, +r}}:
      +sz = note_and_l(N.ElfNote.sized({NOTE}), N.ElfNote.all_sized(r), e)
      +e1 = note_nat_eq(B.Octets.len(name), U32.to_nat(nz), note_and_l(Nat.is_eq(B.Octets.len(name), U32.to_nat(nz)), Nat.is_eq(B.Octets.len(desc), U32.to_nat(dz)), sz))
      +e2 = note_nat_eq(B.Octets.len(desc), U32.to_nat(dz), note_and_r(Nat.is_eq(B.Octets.len(name), U32.to_nat(nz)), Nat.is_eq(B.Octets.len(desc), U32.to_nat(dz)), sz))
      +e1l = {e1l}
      +e2l = {e2l}
      %Equal.sym({L}, {XSc}, {A1}, BL.octets_append_list({W}, {RR})) : {{{GO}(_, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, _)}}, big, al, acc) == {GOAL_R} : {RLN}}}
      %Equal.sym({L}, B.Octets.to_list({W}), {flatw(NL0, DL0)}, note_bytes0(big, al, nz, dz, t, name, desc)) : {{{GO}({app("_", R)}, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, {app("_", R)})}}, big, al, acc) == {GOAL_R} : {RLN}}}
      %Equal.sym({RN}, N.ElfNote.parse.list(big, al, {A2}), {read(NL0, DL0)}, note_parse(big, al, nz, dz, t, {NL0}, {DL0}, {R}, e1l, e2l)) : {{{GO}({A2}, N.ElfNoteHere{{_}}, big, al, acc) == {GOAL_R} : {RLN}}}
      %Equal.sym(B.Octets, B.Octets.of_list({NL0}), name, BL.octets_of_to(name)) : {{{GO}({A2}, {HERE1}, big, al, acc) == {GOAL_R} : {RLN}}}
      %Equal.sym(B.Octets, B.Octets.of_list({DL0}), desc, BL.octets_of_to(desc)) : {{{GO}({A2}, {HERE2}, big, al, acc) == {GOAL_R} : {RLN}}}
      Equal.trans({RLN}, {GO}({A2}, {HERE3}, big, al, acc), {GO}({R}, N.ElfNoteHere{{N.ElfNote.parse.list(big, al, {R})}}, big, al, Con{{{NOTE}, acc}}), {GOAL_R}, note_step({flatw(NL0, DL0)}, {R}, big, al, {NOTE}, {SZ}, acc, note_len(big, al, nz, dz, t, {NL0}, {DL0}, e1l, e2l)), note_list(big, al, r, Con{{{NOTE}, acc}}, note_and_r(N.ElfNote.sized({NOTE}), N.ElfNote.all_sized(r), e)))

def notes_rt(+big: Bool, +al: N.ElfNoteAlign, +ns: List<&2, N.ElfNote>, e: {{N.ElfNote.all_sized(ns) == True{{}} : Bool}}) -> {{N.ElfNote.read_all(big, al, N.ElfNote.write_all(big, al, ns)) == Done{{ns}} : {RLN}}}:
  %note_write_eq(big, al, ns) : {{N.ElfNote.read_all(big, al, _) == Done{{ns}} : {RLN}}}
  note_list(big, al, ns, Nil{{}}, e)

def Laws.notes_round_trip(big, al, ns, e):
  notes_rt(big, al, ns, e)
""")
    return "\n".join(out)
