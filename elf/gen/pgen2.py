# Writes elf/PROOF.bend. The round-trip proofs split every U32 field into its
# 32 bits with a deep pattern, too long to write by hand; the proofs that are
# not about bit patterns are written by hand in gen/proof/*.bend.part and
# copied in. Run from anywhere:
#   python3 elf/gen/pgen2.py [output]   (default: elf/PROOF.bend)
import itertools, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ELF = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True  # no __pycache__ in the package
import accessors  # ENUMS: the named codes


def bits(p, n):
    s = "WNil{}"
    for i in reversed(range(n)):
        s = "WCon{%s%d, %s}" % (p, i, s)
    return s


def u32(p):
    return "U32{%s}" % bits(p, 32)


# field kinds: B (Bool, matched by case), U (U32), W (W64: two U32 halves)
TYPES = {
    "H.ElfHeader": "BBUUUUUWWWUUUUUUU",
    "P.ElfPhdr": "UUWWWWWW",
    "S.ElfShdr": "UUWWWWUUWW",
    "Y.ElfSym": "UWWUUU",
    "R.ElfReloc": "WWW",
    "D.ElfDyn": "WW",
    "V.ElfVersym": "U",
    "V.ElfVerdef": "UUUUUUU",
    "V.ElfVerdaux": "UU",
    "V.ElfVerneed": "UUUUU",
    "V.ElfVernaux": "UUUUU",
}
RTY = "Result<&2, &2, F.ElfError, %s>"


def halves_params(t):
    """parameter names and the record built from them, with W64 fields joined
    from halves"""
    params, fields = [], []
    for i, k in enumerate(TYPES[t]):
        if k == "B":
            params.append(("b%d" % i, "Bool")); fields.append("b%d" % i)
        elif k == "U":
            params.append(("u%d" % i, "U32")); fields.append("u%d" % i)
        else:
            params.append(("h%d" % i, "U32")); params.append(("l%d" % i, "U32"))
            fields.append("W.W64.from_parts(h%d, l%d)" % (i, i))
    return params, "%s{%s}" % (t, ", ".join(fields))


def bits_lemma(name, t, stmt, bools, extra_params=""):
    """stmt(rec) gives the statement; bools: the entry's Bool parameters (each
    Bool, there and among the fields, is matched in every combination)"""
    params, rec = halves_params(t)
    ps = [(b, "Bool") for b in bools] + list(params)
    sig = ", ".join("%s: %s" % p for p in ps) + extra_params
    s = "def %s(%s) -> %s:\n" % (name, sig, stmt(rec))
    names = [p[0] for p in ps]
    s += "  match %s:\n" % " ".join(names)
    nb = sum(1 for _, ty in ps if ty == "Bool")
    for combo in itertools.product(["True{}", "False{}"], repeat=nb):
        pats = []
        bi = 0
        for nm, ty in ps:
            if ty == "Bool":
                pats.append(combo[bi]); bi += 1
            else:
                pats.append(u32(nm + "_"))
        s += "    case %s:\n      {==}\n" % " ".join(pats)
    return s


def list_lemma(name, t, stmt, bits_name, bools, xparam, extra_args, extra_params):
    """match the record, rewrite each W64 field with parts_of, then the bits
    lemma"""
    kinds = TYPES[t]
    fields = ["f%d" % i for i in range(len(kinds))]
    pat = ", ".join(("+" + f) if k == "W" else f for f, k in zip(fields, kinds))
    pre = "".join("%s: Bool, " % b for b in bools)
    s = "def %s(%s%s: %s%s) -> %s:\n" % (name, pre, xparam, t, extra_params, stmt(xparam))
    s += "  match %s:\n    case %s{%s}:\n" % (xparam, t, pat)
    cur = list(fields)
    for i, k in enumerate(kinds):
        if k != "W":
            continue
        motive = list(cur)
        motive[i] = "_"
        s += "      %%WL.parts_of(f%d) : %s\n" % (i, stmt("%s{%s}" % (t, ", ".join(motive))))
        cur[i] = "W.W64.from_parts(W.W64.hi(f%d), W.W64.lo(f%d))" % (i, i)
    args = list(bools)
    for i, k in enumerate(kinds):
        if k == "W":
            args += ["W.W64.hi(f%d)" % i, "W.W64.lo(f%d)" % i]
        else:
            args.append("f%d" % i)
    s += "      %s(%s%s)\n" % (bits_name, ", ".join(args), extra_args)
    return s


def octets_append_sym(a, b):
    return ("Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(%s, %s)), B.append(B.Octets.to_list(%s), B.Octets.to_list(%s)), BL.octets_append_list(%s, %s))" % (a, b, a, b, a, b))


out = []
out.append("""import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S
import ./segments.bend as P
import ./symbols.bend as Y
import ./strtab.bend as T
import ./relocs.bend as R
import ./dynamic.bend as D
import ./notes.bend as N
import ./versions.bend as V
import ./elf.bend as E
import ./LAWS.bend as Laws

# Written by gen/pgen2.py: edit it, or gen/proof/*.bend.part, not this file.
# (word64's and bytes' PROOF.bend are imported for the proofs of their laws,
# which these proofs use; nothing of theirs but the laws is used.)
#
# The round trips go in three steps, never looking inside W64 or Octets:
#   1. bytes' interface law octets_append_list turns the Octets append into a
#      list append;
#   2. word64's interface law parts_of writes each W64 field as its two 32-bit
#      halves joined (from_parts(hi(v), lo(v)));
#   3. with every U32 split into its 32 bits, the reader computes on symbolic
#      bits and meets the writer's input ({==}), in each class, byte order and
#      kind.
""")

# header
HT = "H.ElfHeader"
def hdr_stmt(rec):
    return "{H.ElfHeader.parse.list(H.ElfOptions.default(), B.append(B.Octets.to_list(H.ElfHeader.write(%s)), r)) == Done{H.ElfHeader.normal(%s)} : %s}" % (rec, rec, RTY % HT)
out.append("# The ELF header\n")
out.append(bits_lemma("hdr_bits", HT, hdr_stmt, [], ", r: List<&2, U32>"))
out.append(list_lemma("hdr_list", HT, hdr_stmt, "hdr_bits", [], "h", ", r", ", r: List<&2, U32>"))
out.append("""def hdr_rt(+h: H.ElfHeader, +rest: B.Octets) -> {H.ElfHeader.parse(B.Octets.append(H.ElfHeader.write(h), rest)) == Done{H.ElfHeader.normal(h)} : %s}:
  %%%s : {H.ElfHeader.parse.list(H.ElfOptions.default(), _) == Done{H.ElfHeader.normal(h)} : %s}
  hdr_list(h, B.Octets.to_list(rest))

def Laws.header_round_trip(h, rest):
  hdr_rt(h, rest)
""" % (RTY % HT, octets_append_sym("H.ElfHeader.write(h)", "rest"), RTY % HT))

def trunc_stmt(rec):
    return "{H.ElfHeader.parse(B.Octets.take(Nat.sub(U32.to_nat(H.ElfHeader.size(H.ElfHeader.is64(%s))), 1n), H.ElfHeader.write(%s))) == Fail{F.ElfTruncated{}} : %s}" % (rec, rec, RTY % HT)
out.append(bits_lemma("trunc_bits", HT, trunc_stmt, []))
out.append(list_lemma("Laws.header_truncated", HT, trunc_stmt, "trunc_bits", [], "h", "", "").replace("def Laws.header_truncated(h: H.ElfHeader) -> " + trunc_stmt("h") + ":", "def Laws.header_truncated(h):"))

# Entries: (type, short name, the Bool parameters of parse and write, those of
# normal, those of size)
ENTRIES = [
    ("P.ElfPhdr", "phdr", ["is64", "big"], ["is64"], ["is64"]),
    ("S.ElfShdr", "shdr", ["is64", "big"], ["is64"], ["is64"]),
    ("Y.ElfSym", "sym", ["is64", "big"], ["is64"], ["is64"]),
    ("R.ElfReloc", "rel", ["is64", "big", "rela"], ["is64", "rela"], ["is64", "rela"]),
    ("D.ElfDyn", "dyn", ["is64", "big"], ["is64"], ["is64"]),
    ("V.ElfVersym", "versym", ["big"], [], []),
    ("V.ElfVerdef", "verdef", ["big"], [], []),
    ("V.ElfVerdaux", "verdaux", ["big"], [], []),
    ("V.ElfVerneed", "verneed", ["big"], [], []),
    ("V.ElfVernaux", "vernaux", ["big"], [], []),
]
for T, nm, PL, NL, SL in ENTRIES:
    PA = ", ".join(PL)                            # is64, big
    PB = ", ".join("+%s: Bool" % p for p in PL)   # +is64: Bool, +big: Bool
    NA = "".join("%s, " % p for p in NL)          # "is64, "
    NB = "".join("+%s: Bool, " % p for p in NL)   # "+is64: Bool, "
    SA = ", ".join(SL)
    xs = "xs"
    def stmt(rec, T=T, PA=PA, NA=NA):
        return "{%s.parse.list(%s, B.append(B.Octets.to_list(%s.write(%s, %s)), r)) == Done{%s.normal(%s%s)} : %s}" % (T, PA, T, PA, rec, T, NA, rec, RTY % T)
    def dstmt(rec, T=T, PA=PA, SA=SA):
        return "{r == B.drop(U32.to_nat(%s.size(%s)), B.append(B.Octets.to_list(%s.write(%s, %s)), r)) : List<&2, U32>}" % (T, SA, T, PA, rec)
    out.append("# %s\n" % T)
    out.append(bits_lemma("%s_bits" % nm, T, stmt, PL, ", r: List<&2, U32>"))
    out.append(list_lemma("%s_list" % nm, T, stmt, "%s_bits" % nm, PL, "x", ", r", ", r: List<&2, U32>"))
    out.append(f"""def {nm}_rt({PB}, +x: {T}, +rest: B.Octets) -> {{{T}.parse({PA}, B.Octets.append({T}.write({PA}, x), rest)) == Done{{{T}.normal({NA}x)}} : {RTY % T}}}:
  %{octets_append_sym(f"{T}.write({PA}, x)", "rest")} : {{{T}.parse.list({PA}, _) == Done{{{T}.normal({NA}x)}} : {RTY % T}}}
  {nm}_list({PA}, x, B.Octets.to_list(rest))

def Laws.{nm}_round_trip({PA}, x, rest):
  {nm}_rt({PA}, x, rest)
""")
    # the drop lemma: an entry's bytes are its size
    out.append(bits_lemma("%s_drop_bits" % nm, T, dstmt, PL, ", r: List<&2, U32>"))
    out.append(list_lemma("%s_drop" % nm, T, dstmt, "%s_drop_bits" % nm, PL, "x", ", r", ", r: List<&2, U32>"))
    # the table law, on the structural forms (table.list.ref, write_table.ref,
    # normal_table.ref)
    TY = RTY % ("List<&2, %s>" % T)
    S_ = "U32.to_nat(%s.size(%s))" % (T, SA)
    LX = "B.Octets.to_list(%s.write(%s, x))" % (T, PA)
    LT = "B.Octets.to_list(%s.write_table.ref(%s, xs))" % (T, PA)
    RHS = "Done{%s.normal_table.ref(%sCon{x, xs})}" % (T, NA)
    N = "List.length(&2, %s, xs)" % T
    out.append(f"""def {nm}_table_ref({PB}, xs: List<&2, {T}>) -> {{{T}.table.list.ref({N}, {PA}, {S_}, {LT}) == Done{{{T}.normal_table.ref({NA}xs)}} : {TY}}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +xs}}:
      %{octets_append_sym(f"{T}.write({PA}, x)", f"{T}.write_table.ref({PA}, xs)")} : {{{T}.table.list.ref(List.length(&2, {T}, Con{{x, xs}}), {PA}, {S_}, _) == {RHS} : {TY}}}
      %Equal.sym({RTY % T}, {T}.parse.list({PA}, B.append({LX}, {LT})), Done{{{T}.normal({NA}x)}}, {nm}_list({PA}, x, {LT})) : {{F.elf_cons({T}, _, {T}.table.list.ref({N}, {PA}, {S_}, B.drop({S_}, B.append({LX}, {LT})))) == {RHS} : {TY}}}
      %{nm}_drop({PA}, x, {LT}) : {{F.elf_cons({T}, Done{{{T}.normal({NA}x)}}, {T}.table.list.ref({N}, {PA}, {S_}, _)) == {RHS} : {TY}}}
      %Equal.sym({TY}, {T}.table.list.ref({N}, {PA}, {S_}, {LT}), Done{{{T}.normal_table.ref({NA}xs)}}, {nm}_table_ref({PA}, xs)) : {{F.elf_cons({T}, Done{{{T}.normal({NA}x)}}, _) == {RHS} : {TY}}}
      {{==}}

# The tail-recursive table reader is the structural one: the entries read so
# far, reversed in acc, go back in front of the structural reader's answer.

def {nm}_fin(rs: List<&2, {T}>, m: {TY}) -> {TY}:
  match m:
    case Fail{{e}}:
      Fail{{e}}
    case Done{{l}}:
      Done{{F.elf_rev_onto({T}, rs, l)}}

def {nm}_fin2(acc: {TY}, m: {TY}) -> {TY}:
  match acc:
    case Fail{{e}}:
      Fail{{e}}
    case Done{{rs}}:
      {nm}_fin(rs, m)

def {nm}_push(+r: {RTY % T}, +rs: List<&2, {T}>, +m: {TY}) -> {{{nm}_fin2(F.elf_push({T}, r, rs), m) == {nm}_fin(rs, F.elf_cons({T}, r, m)) : {TY}}}:
  match r:
    case Done{{x}}:
      match m:
        case Done{{l}}:
          {{==}}
        case Fail{{e}}:
          {{==}}
    case Fail{{e}}:
      match m:
        case Done{{l}}:
          {{==}}
        case Fail{{f}}:
          {{==}}

def {nm}_go(n: Nat, +acc: {TY}, {PB}, +step: Nat, +ys: List<&2, U32>) -> {{{T}.table.go(n, acc, {PA}, step, ys) == {nm}_fin2(acc, {T}.table.list.ref(n, {PA}, step, ys)) : {TY}}}:
  match n:
    case 0n:
      match acc:
        case Fail{{e}}:
          {{==}}
        case Done{{rs}}:
          {{==}}
    case 1n+(+p):
      match acc:
        case Fail{{e}}:
          {{==}}
        case Done{{+rs}}:
          Equal.trans({TY}, {T}.table.go(p, F.elf_push({T}, {T}.parse.list({PA}, ys), rs), {PA}, step, B.drop(step, ys)), {nm}_fin2(F.elf_push({T}, {T}.parse.list({PA}, ys), rs), {T}.table.list.ref(p, {PA}, step, B.drop(step, ys))), {nm}_fin(rs, F.elf_cons({T}, {T}.parse.list({PA}, ys), {T}.table.list.ref(p, {PA}, step, B.drop(step, ys)))), {nm}_go(p, F.elf_push({T}, {T}.parse.list({PA}, ys), rs), {PA}, step, B.drop(step, ys)), {nm}_push({T}.parse.list({PA}, ys), rs, {T}.table.list.ref(p, {PA}, step, B.drop(step, ys))))

def {nm}_fin_nil(+m: {TY}) -> {{{nm}_fin(Nil{{}}, m) == m : {TY}}}:
  match m:
    case Fail{{e}}:
      {{==}}
    case Done{{l}}:
      {{==}}

def {nm}_table_eq(+n: Nat, {PB}, +step: Nat, +ys: List<&2, U32>) -> {{{T}.table.list.ref(n, {PA}, step, ys) == {T}.table.list(n, {PA}, step, ys) : {TY}}}:
  Equal.sym({TY}, {T}.table.list(n, {PA}, step, ys), {T}.table.list.ref(n, {PA}, step, ys), Equal.trans({TY}, {T}.table.go(n, Done{{Nil{{}}}}, {PA}, step, ys), {nm}_fin(Nil{{}}, {T}.table.list.ref(n, {PA}, step, ys)), {T}.table.list.ref(n, {PA}, step, ys), {nm}_go(n, Done{{Nil{{}}}}, {PA}, step, ys), {nm}_fin_nil({T}.table.list.ref(n, {PA}, step, ys))))

# The tail-recursive writer is the structural one: writing the reversed
# entries rs after xs reversed onto them is writing rs onto the structural
# table of xs.

def {nm}_wgo({PB}, +xs: List<&2, {T}>, +rs: List<&2, {T}>) -> {{{T}.write_table.go({PA}, F.elf_rev_onto({T}, xs, rs), B.Octets.empty()) == {T}.write_table.go({PA}, rs, {T}.write_table.ref({PA}, xs)) : B.Octets}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{x, t}}:
      {nm}_wgo({PA}, t, Con{{x, rs}})

def {nm}_write_eq({PB}, +xs: List<&2, {T}>) -> {{{T}.write_table.ref({PA}, xs) == {T}.write_table({PA}, xs) : B.Octets}}:
  Equal.sym(B.Octets, {T}.write_table({PA}, xs), {T}.write_table.ref({PA}, xs), {nm}_wgo({PA}, xs, Nil{{}}))

# The same for the normal forms: the entries done so far, reversed in acc

def {nm}_ngo({NB}+xs: List<&2, {T}>, +acc: List<&2, {T}>) -> {{{T}.normal_table.go({NA}xs, acc) == F.elf_rev_onto({T}, acc, {T}.normal_table.ref({NA}xs)) : List<&2, {T}>}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{x, t}}:
      {nm}_ngo({NA}t, Con{{{T}.normal({NA}x), acc}})

def {nm}_normal_eq({NB}+xs: List<&2, {T}>) -> {{{T}.normal_table.ref({NA}xs) == {T}.normal_table({NA}xs) : List<&2, {T}>}}:
  Equal.sym(List<&2, {T}>, {T}.normal_table({NA}xs), {T}.normal_table.ref({NA}xs), {nm}_ngo({NA}xs, Nil{{}}))

# the table law: the tail-recursive forms rewritten to the structural ones
def {nm}_table({PB}, +xs: List<&2, {T}>) -> {{{T}.read_table({PA}, {N}, {S_}, {T}.write_table({PA}, xs)) == Done{{{T}.normal_table({NA}xs)}} : {TY}}}:
  %{nm}_write_eq({PA}, xs) : {{{T}.read_table({PA}, {N}, {S_}, _) == Done{{{T}.normal_table({NA}xs)}} : {TY}}}
  %{nm}_normal_eq({NA}xs) : {{{T}.read_table({PA}, {N}, {S_}, {T}.write_table.ref({PA}, xs)) == Done{{_}} : {TY}}}
  %{nm}_table_eq({N}, {PA}, {S_}, {LT}) : {{_ == Done{{{T}.normal_table.ref({NA}xs)}} : {TY}}}
  {nm}_table_ref({PA}, xs)

def Laws.{nm}_table_round_trip({PA}, xs):
  {nm}_table({PA}, xs)
""")

out.append("""# Rejection

# False is not True
def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def bool_absurd(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_disc(_)
  Unit{}

def Laws.rejects_bad_magic(o, e):
  %Equal.sym(Bool, H.ElfHeader.has_magic(o), False{}, e) : {H.ElfHeader.parse.magic(_, True{}, B.Octets.to_list(o)) == Fail{F.ElfBadMagic{}} : Result<&2, &2, F.ElfError, H.ElfHeader>}
  {==}

# a list shorter than n does not have n bytes (stated on bytes' mask, which
# is what to_list(of_list(xs)) is, by bytes' law octets_to_of)
def short_lemma(n: Nat, xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), n) == True{} : Bool}) -> {False{} == F.elf_at_least(n, B.mask(xs)) : Bool}:
  match n xs:
    case 0n Nil{}:
      Empty.absurd({False{} == F.elf_at_least(0n, B.mask(Nil{})) : Bool}, bool_absurd(e))
    case 0n Con{h, t}:
      Empty.absurd({False{} == F.elf_at_least(0n, B.mask(Con{h, t})) : Bool}, bool_absurd(e))
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      short_lemma(p, t, e)

# whether or not the magic is there, a list that short fails
def short_magic(b: Bool, +xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), 52n) == True{} : Bool}) -> {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse.magic(b, True{}, B.Octets.to_list(B.Octets.of_list(xs)))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse.sized(F.elf_at_least(52n, _), True{}, B.Octets.to_list(B.Octets.of_list(xs)))) == True{} : Bool}
      %short_lemma(52n, xs, e) : {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse.sized(_, True{}, B.Octets.to_list(B.Octets.of_list(xs)))) == True{} : Bool}
      {==}
    case False{}:
      {==}

def short_rt(+xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), 52n) == True{} : Bool}) -> {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse(B.Octets.of_list(xs))) == True{} : Bool}:
  short_magic(H.ElfHeader.has_magic.list(B.Octets.to_list(B.Octets.of_list(xs))), xs, e)

def Laws.rejects_short(xs, e):
  short_rt(xs, e)
""")

# Named codes: of_code(code(k)) is k, for every named k
for t, es in accessors.ENUMS.items():
    law = {"ElfDynTag": "dyn_tag_code"}[t]
    s = "# every named %s's code names it\ndef Laws.%s(k):\n  match k:\n" % (t, law)
    for c, _, _ in es:
        s += "    case D.%s{}:\n      {==}\n" % c
    out.append(s)

# The note proofs (gen/pnotes.py)
import pnotes
out.append(pnotes.gen())

# The proofs written by hand
for part in sorted(os.listdir(os.path.join(HERE, "proof"))):
    if part.endswith(".bend.part"):
        with open(os.path.join(HERE, "proof", part)) as f:
            out.append(f.read().rstrip("\n") + "\n")

# Vectors: every law of LAWS.bend without a "for" line, by computation
with open(os.path.join(ELF, "LAWS.bend")) as f:
    laws = re.findall(r"^law (\w+):\n((?:  .*\n)*)", f.read(), re.M)
out.append("# Vectors: by computation\n")
for name, body in laws:
    if not re.search(r"^  (for|exs) ", body, re.M):
        out.append("def Laws.%s():\n  {==}\n" % name)

dest = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ELF, "PROOF.bend")
with open(dest, "w", newline="\n") as f:
    f.write("\n".join(out))
