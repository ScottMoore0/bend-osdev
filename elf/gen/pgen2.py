# Writes elf/PROOF.bend: the round-trip proofs split every U32 field into its
# 32 bits with a deep pattern, too long to write by hand. Run from anywhere:
#   python3 elf/gen/pgen2.py [output]   (default: elf/PROOF.bend)
import os, sys

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
}
BOOLS = [("True{}", "True{}"), ("True{}", "False{}"), ("False{}", "True{}"), ("False{}", "False{}")]
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


def bits_lemma(name, t, stmt, entry, extra_params=""):
    """stmt(rec) gives the statement; entry: is64 and big are parameters"""
    params, rec = halves_params(t)
    ps = list(params)
    if entry:
        ps = [("is64", "Bool"), ("big", "Bool")] + ps
    sig = ", ".join("%s: %s" % p for p in ps) + extra_params
    s = "def %s(%s) -> %s:\n" % (name, sig, stmt(rec))
    names = [p[0] for p in ps]
    s += "  match %s:\n" % " ".join(names)
    for b in BOOLS:
        pats = []
        bi = 0
        for nm, ty in ps:
            if ty == "Bool":
                pats.append(b[bi]); bi += 1
            else:
                pats.append(u32(nm + "_"))
        s += "    case %s:\n      {==}\n" % " ".join(pats)
    return s


def list_lemma(name, t, stmt, bits_name, entry, xparam, extra_args, extra_params):
    """match the record, rewrite each W64 field with parts_of, then the bits
    lemma"""
    kinds = TYPES[t]
    fields = ["f%d" % i for i in range(len(kinds))]
    pat = ", ".join(("+" + f) if k == "W" else f for f, k in zip(fields, kinds))
    pre = "is64: Bool, big: Bool, " if entry else ""
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
    args = []
    for i, k in enumerate(kinds):
        if k == "W":
            args += ["W.W64.hi(f%d)" % i, "W.W64.lo(f%d)" % i]
        else:
            args.append("f%d" % i)
    if entry:
        args = ["is64", "big"] + args
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
import ./elf.bend as E
import ./LAWS.bend as Laws

# The round trips go in three steps, never looking inside W64 or Octets:
#   1. bytes' interface law octets_append_list turns the Octets append into a
#      list append;
#   2. word64's interface law parts_of writes each W64 field as its two 32-bit
#      halves joined (from_parts(hi(v), lo(v)));
#   3. with every U32 split into its 32 bits, the reader computes on symbolic
#      bits and meets the writer's input ({==}), in each class and byte order.
""")

# header
HT = "H.ElfHeader"
def hdr_stmt(rec):
    return "{H.ElfHeader.parse.list(H.ElfOptions.default(), B.append(B.Octets.to_list(H.ElfHeader.write(%s)), r)) == Done{H.ElfHeader.normal(%s)} : %s}" % (rec, rec, RTY % HT)
out.append("# The ELF header\n")
out.append(bits_lemma("hdr_bits", HT, hdr_stmt, False, ", r: List<&2, U32>"))
out.append(list_lemma("hdr_list", HT, hdr_stmt, "hdr_bits", False, "h", ", r", ", r: List<&2, U32>"))
out.append("""def hdr_rt(+h: H.ElfHeader, +rest: B.Octets) -> {H.ElfHeader.parse(B.Octets.append(H.ElfHeader.write(h), rest)) == Done{H.ElfHeader.normal(h)} : %s}:
  %%%s : {H.ElfHeader.parse.list(H.ElfOptions.default(), _) == Done{H.ElfHeader.normal(h)} : %s}
  hdr_list(h, B.Octets.to_list(rest))

def Laws.header_round_trip(h, rest):
  hdr_rt(h, rest)
""" % (RTY % HT, octets_append_sym("H.ElfHeader.write(h)", "rest"), RTY % HT))

def trunc_stmt(rec):
    return "{H.ElfHeader.parse(B.Octets.take(Nat.sub(U32.to_nat(H.ElfHeader.size(H.ElfHeader.is64(%s))), 1n), H.ElfHeader.write(%s))) == Fail{F.ElfTruncated{}} : %s}" % (rec, rec, RTY % HT)
out.append(bits_lemma("trunc_bits", HT, trunc_stmt, False))
out.append(list_lemma("Laws.header_truncated", HT, trunc_stmt, "trunc_bits", False, "h", "", "").replace("def Laws.header_truncated(h: H.ElfHeader) -> " + trunc_stmt("h") + ":", "def Laws.header_truncated(h):"))

# entries
ENTRIES = [("P.ElfPhdr", "phdr", "p", "ps"), ("S.ElfShdr", "shdr", "s", "ss"), ("Y.ElfSym", "sym", "s", "ss")]
for T, nm, x, xs in ENTRIES:
    def stmt(rec, T=T):
        return "{%s.parse.list(is64, big, B.append(B.Octets.to_list(%s.write(is64, big, %s)), r)) == Done{%s.normal(is64, %s)} : %s}" % (T, T, rec, T, rec, RTY % T)
    def dstmt(rec, T=T):
        return "{r == B.drop(U32.to_nat(%s.size(is64)), B.append(B.Octets.to_list(%s.write(is64, big, %s)), r)) : List<&2, U32>}" % (T, T, rec)
    out.append("# %s\n" % T)
    out.append(bits_lemma("%s_bits" % nm, T, stmt, True, ", r: List<&2, U32>"))
    out.append(list_lemma("%s_list" % nm, T, stmt, "%s_bits" % nm, True, "x", ", r", ", r: List<&2, U32>"))
    out.append("""def %s_rt(+is64: Bool, +big: Bool, +x: %s, +rest: B.Octets) -> {%s.parse(is64, big, B.Octets.append(%s.write(is64, big, x), rest)) == Done{%s.normal(is64, x)} : %s}:
  %%%s : {%s.parse.list(is64, big, _) == Done{%s.normal(is64, x)} : %s}
  %s_list(is64, big, x, B.Octets.to_list(rest))

def Laws.%s_round_trip(is64, big, x, rest):
  %s_rt(is64, big, x, rest)
""" % (nm, T, T, T, T, RTY % T, octets_append_sym("%s.write(is64, big, x)" % T, "rest"), T, T, RTY % T, nm, nm, nm))
    # the drop lemma: an entry's bytes are its size
    out.append(bits_lemma("%s_drop_bits" % nm, T, dstmt, True, ", r: List<&2, U32>"))
    out.append(list_lemma("%s_drop" % nm, T, dstmt, "%s_drop_bits" % nm, True, "x", ", r", ", r: List<&2, U32>"))
    # the table law
    TY = RTY % ("List<&2, %s>" % T)
    S_ = "U32.to_nat(%s.size(is64))" % T
    LX = "B.Octets.to_list(%s.write(is64, big, x))" % T
    LT = "B.Octets.to_list(%s.write_table(is64, big, xs))" % T
    RHS = "Done{%s.normal_table(is64, Con{x, xs})}" % T
    N = "List.length(&2, %s, xs)" % T
    out.append(f"""def {nm}_table(+is64: Bool, +big: Bool, {xs}: List<&2, {T}>) -> {{{T}.read_table(is64, big, List.length(&2, {T}, {xs}), {S_}, {T}.write_table(is64, big, {xs})) == Done{{{T}.normal_table(is64, {xs})}} : {TY}}}:
  match {xs}:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +xs}}:
      %{octets_append_sym(f"{T}.write(is64, big, x)", f"{T}.write_table(is64, big, xs)")} : {{{T}.table.list(List.length(&2, {T}, Con{{x, xs}}), is64, big, {S_}, _) == {RHS} : {TY}}}
      %Equal.sym({RTY % T}, {T}.parse.list(is64, big, B.append({LX}, {LT})), Done{{{T}.normal(is64, x)}}, {nm}_list(is64, big, x, {LT})) : {{F.elf_cons({T}, _, {T}.table.list({N}, is64, big, {S_}, B.drop({S_}, B.append({LX}, {LT})))) == {RHS} : {TY}}}
      %{nm}_drop(is64, big, x, {LT}) : {{F.elf_cons({T}, Done{{{T}.normal(is64, x)}}, {T}.table.list({N}, is64, big, {S_}, _)) == {RHS} : {TY}}}
      %Equal.sym({TY}, {T}.read_table(is64, big, {N}, {S_}, {T}.write_table(is64, big, xs)), Done{{{T}.normal_table(is64, xs)}}, {nm}_table(is64, big, xs)) : {{F.elf_cons({T}, Done{{{T}.normal(is64, x)}}, _) == {RHS} : {TY}}}
      {{==}}

def Laws.{nm}_table_round_trip(is64, big, {xs}):
  {nm}_table(is64, big, {xs})
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

# a list shorter than n does not have n bytes
def short_lemma(n: Nat, xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), n) == True{} : Bool}) -> {False{} == F.elf_at_least(n, B.Octets.to_list(B.Octets.of_list(xs))) : Bool}:
  match n xs:
    case 0n Nil{}:
      Empty.absurd({False{} == F.elf_at_least(0n, B.Octets.to_list(B.Octets.of_list(Nil{}))) : Bool}, bool_absurd(e))
    case 0n Con{h, t}:
      Empty.absurd({False{} == F.elf_at_least(0n, B.Octets.to_list(B.Octets.of_list(Con{h, t}))) : Bool}, bool_absurd(e))
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      short_lemma(p, t, e)

# whether or not the magic is there, a list that short fails
def short_magic(b: Bool, xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), 52n) == True{} : Bool}) -> {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse.magic(b, True{}, B.Octets.to_list(B.Octets.of_list(xs)))) == True{} : Bool}:
  match b:
    case True{}:
      %short_lemma(52n, xs, e) : {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse.sized(_, True{}, B.Octets.to_list(B.Octets.of_list(xs)))) == True{} : Bool}
      {==}
    case False{}:
      {==}

def short_rt(+xs: List<&2, U32>, e: {Nat.is_lt(List.length(&2, U32, xs), 52n) == True{} : Bool}) -> {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse(B.Octets.of_list(xs))) == True{} : Bool}:
  short_magic(H.ElfHeader.has_magic.list(B.Octets.to_list(B.Octets.of_list(xs))), xs, e)

def Laws.rejects_short(xs, e):
  short_rt(xs, e)
""")

VECTORS = ["vector_x86_64", "vector_ppc32_big_endian", "rejects_bad_class", "rejects_bad_data", "rejects_bad_version", "version_unchecked", "extended_shnum", "phdrs_past_end", "string_text", "string_data", "string_empty", "string_past_end", "string_unterminated", "sym_info", "sym_bind_type", "whole_file"]
out.append("# Vectors: by computation\n")
for v in VECTORS:
    out.append("def Laws.%s():\n  {==}\n" % v)

dest = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "PROOF.bend")
with open(dest, "w", newline="\n") as f:
    f.write("\n".join(out))
