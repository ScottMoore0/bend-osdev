#!/usr/bin/env python3
"""Writes hashes/LAWS.bend and hashes/PROOF.bend.

  python3 gen/laws.py           rewrite both files
  python3 gen/laws.py --check   only check that they are up to date

The laws, for each hash of the table below:
  * <h>_streaming: update(s, a ++ b) == update(update(s, a), b), for every
    state and every a, b: the engine's md_streaming (stated once, for every
    chaining value type and compression function) at the hash's own defs;
  * <h>_split, <h>_split3: the digest in two or three pieces of any split
    is the one-shot digest (from streaming);
  * <h>_length: final(s) has the digest's length for every state s, and
    <h>_digest_length: digest(m) does for every message m (the digest is
    the bytes of a chaining value, whatever value it is);
  * vectors: the specification's own examples, by computation (for
    Streebog, whose whole digests run past --verdict's kernel fuel, the
    intermediate values RFC 6986 prints instead: streebog_laws below).
Michael has the same laws under every key, and the refusal of a key that
is not eight bytes.

Why the proofs hold for every input. update is a fold of a step function
over the message's bytes (hashes.bend), so feeding a ++ b is feeding a and
then b, by induction on a, whatever the step does; nothing about the
compression function, the buffer or the block count is needed. The digest
length needs only that the digest is the bytes of the chaining value's
words, a list of fixed shape for every value of its words.

The vectors are the specifications' values (ref/model.py's tables, which
the Python models are checked against first), not computed by this script.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..")
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(PKG, "ref"))
import model  # noqa: E402


def octets(bs):
    try:
        s = bs.decode("ascii")
        if all(32 <= ord(c) < 127 and c not in '"\\' for c in s):
            return 'B.Octets.of_string("%s")' % s
    except UnicodeDecodeError:
        pass
    return "B.Octets.of_list([%s])" % ", ".join(str(b) for b in bs)


def digest_lit(hexs):
    return "B.Octets.of_list([%s])" % ", ".join(str(b) for b in bytes.fromhex(hexs))


def md(field, out):
    """the length proof of a Merkle-Damgard final (HsMd.final_md)"""
    def term(C, compress, s):
        return ("%s(Hs.HsMd.cv(~%s, Hs.hs.md.feed(~%s, ~%s, ~63, Hs.HsMd.md_pad(~63, Hs.HsMd.count(~%s, %s), "
                "Hs.%s(Hs.HsMd.bits(~%s, ~63, %s))), %s)))" % (out, C, C, compress, C, s, field, C, s, s))
    return term


def stb(out):
    return lambda C, compress, s: "%s(ST.hs.stb.finish(%s))" % (out, s)


# name, title, module (alias, file), def prefix, chaining value, digest
# size, the length proof, vectors (message, digest in memory order)
HASHES = [
    dict(name="md4", title="MD4 (RFC 1320)", alias="M4", file="md4", p="M4.HsMd4", C="Hs.HsW4", n=16,
         init="M4.HsMd4.init()", length=md("hs.len.le", "w4le_len"),
         vectors=[("rfc1320_%d" % i, m, v) for i, (m, v) in enumerate(zip(model.ASCII, model.MD4_V), 1)],
         cite="RFC 1320, appendix A.5 (the test suite)"),
    dict(name="md5", title="MD5 (RFC 1321)", alias="M5", file="md5", p="M5.HsMd5", C="Hs.HsW4", n=16,
         init="M5.HsMd5.init()", length=md("hs.len.le", "w4le_len"),
         vectors=[("rfc1321_%d" % i, m, v) for i, (m, v) in enumerate(zip(model.ASCII, model.MD5_V), 1)],
         cite="RFC 1321, appendix A.5 (the test suite)"),
    dict(name="sha1", title="SHA-1 (FIPS 180-4)", alias="S1", file="sha1", p="S1.HsSha1", C="Hs.HsW5", n=20,
         init="S1.HsSha1.init()", length=md("hs.len.be", "w5be_len"),
         vectors=[("fips_%d" % i, m, v) for i, (m, v) in enumerate(model.SHA1_V, 1)],
         cite="FIPS 180-4's examples (NIST's SHA-1 example values): \"abc\" and the 448-bit message"),
    dict(name="ripemd160", title="RIPEMD-160", alias="RM", file="ripemd160", p="RM.HsRipemd160", C="Hs.HsW5", n=20,
         init="RM.HsRipemd160.init()", length=md("hs.len.le", "w5le_len"),
         vectors=[("paper_%d" % i, m, v) for i, (m, v) in enumerate(model.RMD_V, 1)],
         cite="the test values of Dobbertin, Bosselaers and Preneel (the RIPEMD-160 page)"),
    dict(name="sm3", title="SM3 (GB/T 32905)", alias="SM", file="sm3", p="SM.HsSm3", C="Hs.HsW8", n=32,
         init="SM.HsSm3.init()", length=md("hs.len.be", "w8be_len"),
         vectors=[("example_%d" % i, m, v) for i, (m, v) in enumerate(model.SM3_V, 1)],
         cite="draft-shen-sm3-hash-01, examples 1 and 2"),
    dict(name="streebog512", title="Streebog-512 (RFC 6986)", alias="ST", file="streebog", p="ST.HsStreebog", C="ST.HsStbCv", n=64,
         init="ST.HsStreebog.init512()", final="ST.HsStreebog.final512", digest="ST.HsStreebog.digest512",
         compress="ST.HsStreebog.compress", update="ST.HsStreebog.update", length=stb("stb512_len"),
         vectors=[], cite=None),  # see streebog_laws
    dict(name="streebog256", title="Streebog-256 (RFC 6986)", alias="ST", file="streebog", p="ST.HsStreebog", C="ST.HsStbCv", n=32,
         init="ST.HsStreebog.init256()", final="ST.HsStreebog.final256", digest="ST.HsStreebog.digest256",
         compress="ST.HsStreebog.compress", update="ST.HsStreebog.update", length=stb("stb256_len"),
         vectors=[], cite=None),  # see streebog_laws
]

for h in HASHES:
    h.setdefault("final", h["p"] + ".final")
    h.setdefault("digest", h["p"] + ".digest")
    h.setdefault("update", h["p"] + ".update")
    h.setdefault("compress", h["p"] + ".compress")

IMPORTS = """import Base
import ../bytes/bytes.bend as B
import ./hashes.bend as Hs
import ./md4.bend as M4
import ./md5.bend as M5
import ./sha1.bend as S1
import ./ripemd160.bend as RM
import ./sm3.bend as SM
import ./streebog.bend as ST
import ./michael.bend as MI
"""

LAWS_HEAD = '''# Generated by gen/laws.py; do not edit by hand.
#
# The laws of the hashes, for every input where they are proved:
# streaming (update over a ++ b is update over a, then b, from every
# state), the digest in any pieces equals the one-shot digest, and the
# digest's length; then the specifications' vectors. The engine's streaming
# law is stated once, for every chaining value and compression function;
# each hash's is that law at its own defs.
''' + IMPORTS + '''
# The engine (hashes.bend), for every chaining value type, compression
# function and block size: a ++ b is a, then b, from every state
law md_streaming:
  for ~C: Data
  for ~compress: C -> List<&2, U32> -> C
  for ~last: U32
  for s: Hs.HsMdState<C>
  for +a: B.Octets
  for +b: B.Octets
  {Hs.HsMd.update(~C, ~compress, ~last, s, B.Octets.append(a, b)) == Hs.HsMd.update(~C, ~compress, ~last, Hs.HsMd.update(~C, ~compress, ~last, s, a), b) : Hs.HsMdState<C>}
'''

PROOF_HEAD = '''# Generated by gen/laws.py; do not edit by hand.
''' + IMPORTS + '''import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# The engine: feeding xs ++ ys is feeding xs, then ys (induction on xs)
def feed_append(~C: Data, ~compress: C -> List<&2, U32> -> C, ~last: U32, xs: List<&2, U32>, +ys: List<&2, U32>, s: Hs.HsMdState<C>) -> {Hs.hs.md.feed(~C, ~compress, ~last, B.append(xs, ys), s) == Hs.hs.md.feed(~C, ~compress, ~last, ys, Hs.hs.md.feed(~C, ~compress, ~last, xs, s)) : Hs.HsMdState<C>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      feed_append(~C, ~compress, ~last, t, ys, Hs.hs.md.step(~C, ~compress, ~last, s, x))

def Laws.md_streaming(C, compress, last, s, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {Hs.hs.md.feed(~C, ~compress, ~last, _, s) == Hs.HsMd.update(~C, ~compress, ~last, Hs.HsMd.update(~C, ~compress, ~last, s, a), b) : Hs.HsMdState<C>}
  feed_append(~C, ~compress, ~last, B.Octets.to_list(a), B.Octets.to_list(b), s)

# Lengths: an Octets made from a list has the list's length; the bytes of
# a chaining value are a list of fixed shape whatever its words are
def mask_len(xs: List<&2, U32>) -> {B.len(B.mask(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mask_len(t) : {B.len(B.mask(Con{h, t})) == 1n+_ : Nat}
      {==}

def octets_len_of(+xs: List<&2, U32>) -> {B.Octets.len(B.Octets.of_list(xs)) == B.len(xs) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(xs)), B.len(B.Octets.to_list(B.Octets.of_list(xs))), BL.octets_len_list(B.Octets.of_list(xs))) : {_ == B.len(xs) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {B.len(_) == B.len(xs) : Nat}
  mask_len(xs)
'''


def app(xs):
    t = xs[-1]
    for x in reversed(xs[:-1]):
        t = "B.append(%s, %s)" % (x, t)
    return t


def len_lemma(name, ty, ctor, nwords, order, n, out, first=0):
    """len(out(x)) == n for every x: the words' bytes, through octets_len_of"""
    vs = ["a%d" % i for i in range(nwords)]
    used = vs[first:]
    lst = app(["B.%s(%s)" % (order, v) for v in used])
    pat = "%s{%s}" % (ctor, ", ".join("+" + v if v in used else v for v in vs))
    return '''def %s_list(%s) -> {B.len(%s) == %dn : Nat}:
  match %s:
    case %s:
      {==}

def %s(x: %s) -> {B.Octets.len(%s(x)) == %dn : Nat}:
  match x:
    case %s:
      %%Equal.sym(Nat, B.Octets.len(B.Octets.of_list(%s)), B.len(%s), octets_len_of(%s)) : {_ == %dn : Nat}
      %s_list(%s)
''' % (name, ", ".join("%s: U32" % v for v in used), lst, n, " ".join(used), " ".join("U32{w%s}" % v for v in used),
       name, ty, out, n, pat, lst, lst, lst, n, name, ", ".join(used))


LEN_LEMMAS = [
    len_lemma("w2le_len", "Hs.HsW2", "Hs.HsW2", 2, "le32", 8, "Hs.HsW2.le"),
    len_lemma("w4le_len", "Hs.HsW4", "Hs.HsW4", 4, "le32", 16, "Hs.HsW4.le"),
    len_lemma("w5le_len", "Hs.HsW5", "Hs.HsW5", 5, "le32", 20, "Hs.HsW5.le"),
    len_lemma("w5be_len", "Hs.HsW5", "Hs.HsW5", 5, "be32", 20, "Hs.HsW5.be"),
    len_lemma("w8be_len", "Hs.HsW8", "Hs.HsW8", 8, "be32", 32, "Hs.HsW8.be"),
    len_lemma("stb512_len", "Hs.HsW16", "Hs.HsW16", 16, "le32", 64, "ST.hs.stb.out512"),
    len_lemma("stb256_len", "Hs.HsW16", "Hs.HsW16", 16, "le32", 32, "ST.hs.stb.out256", first=8),
]

LAWS, PROOFS = [], []


def law(name, comment, params, stmt):
    LAWS.append("# %s\nlaw %s:\n%s  %s\n" % (comment, name, "".join("  for %s\n" % p for p in params), stmt))


def hash_laws(h):
    n, t, S = h["name"], h["title"], "Hs.HsMdState<%s>" % h["C"]
    U = lambda s, m: "%s(%s, %s)" % (h["update"], s, m)
    F = lambda s: "%s(%s)" % (h["final"], s)
    D = lambda m: "%s(%s)" % (h["digest"], m)
    I = h["init"]
    LAWS.append("# %s (%s.bend)\n" % (t, h["file"]))
    law("%s_streaming" % n, "%s: update over a ++ b is update over a, then b, from every state" % t,
        ["s: %s" % S, "+a: B.Octets", "+b: B.Octets"], "{%s == %s : %s}" % (U("s", "B.Octets.append(a, b)"), U(U("s", "a"), "b"), S))
    PROOFS.append("def Laws.%s_streaming(s, a, b):\n  Laws.md_streaming(~%s, ~%s, ~63, s, a, b)\n" % (n, h["C"], h["compress"]))
    law("%s_split" % n, "%s: the digest in two pieces is the one-shot digest, for every split" % t,
        ["+a: B.Octets", "+b: B.Octets"], "{%s == %s : B.Octets}" % (F(U(U(I, "a"), "b")), D("B.Octets.append(a, b)")))
    PROOFS.append("def Laws.%s_split(a, b):\n  %%Laws.%s_streaming(%s, a, b) : {%s == %s : B.Octets}\n  {==}\n"
                  % (n, n, I, F("_"), D("B.Octets.append(a, b)")))
    abc = "B.Octets.append(a, B.Octets.append(b, c))"
    law("%s_split3" % n, "%s: and in three pieces" % t, ["+a: B.Octets", "+b: B.Octets", "+c: B.Octets"],
        "{%s == %s : B.Octets}" % (F(U(U(U(I, "a"), "b"), "c")), D(abc)))
    PROOFS.append("def Laws.%s_split3(a, b, c):\n  %%Laws.%s_streaming(%s, b, c) : {%s == %s : B.Octets}\n"
                  "  %%Laws.%s_streaming(%s, a, B.Octets.append(b, c)) : {%s == %s : B.Octets}\n  {==}\n"
                  % (n, n, U(I, "a"), F("_"), D(abc), n, I, F("_"), D(abc)))
    law("%s_length" % n, "%s: the digest of every state has %d bytes" % (t, h["n"]), ["+s: %s" % S],
        "{B.Octets.len(%s) == %dn : Nat}" % (F("s"), h["n"]))
    PROOFS.append("def Laws.%s_length(s):\n  %s\n" % (n, h["length"](h["C"], h["compress"], "s")))
    law("%s_digest_length" % n, "%s: the digest of every message has %d bytes" % (t, h["n"]), ["+m: B.Octets"],
        "{B.Octets.len(%s) == %dn : Nat}" % (D("m"), h["n"]))
    PROOFS.append("def Laws.%s_digest_length(m):\n  Laws.%s_length(%s)\n" % (n, n, U(I, "m")))
    for vn, m, v in h["vectors"]:
        law("%s_%s" % (n, vn), "%s: %s" % (t, h["cite"]), [], "{%s == %s : B.Octets}" % (D(octets(m)), digest_lit(v)))
        PROOFS.append("def Laws.%s_%s():\n  {==}\n" % (n, vn))


def streebog_laws():
    """Streebog's whole digests run past --verdict's kernel fuel (one
    compression fits, two do not), so its vectors are the steps RFC 6986's
    example 1 prints: LPS(0), and the first two compressions"""
    LAWS.append("# Streebog's transformations (streebog.bend): RFC 6986, section 10.1, example 1\n")
    z = "B.Octets.zeros(64n)"
    m1 = model.STB_M1 + bytes([1])
    for name, comment, lhs, v in [
            ("streebog_lps_zero", "K = LPS(h xor N) = LPS(0^512)", "ST.HsStreebog.lps(%s)" % z, model.STB_EX1[0]),
            ("streebog_g_example1", "the first compression, g_N(h, m) with h = N = 0 and m the padded M1",
             "ST.HsStreebog.g(%s, %s, %s)" % (z, z, octets(m1)), model.STB_EX1[1]),
            ("streebog_g0_example1", "g_0(h, N) after it, N = 504",
             "ST.HsStreebog.g(%s, %s, B.Octets.of_list([248, 1]))" % (z, digest_lit(bytes.fromhex(model.STB_EX1[1])[::-1].hex())), model.STB_EX1[2])]:
        law(name, "Streebog-512, %s (RFC 6986 prints it most significant byte first)" % comment, [],
            "{%s == %s : B.Octets}" % (lhs, digest_lit(bytes.fromhex(v)[::-1].hex())))
        PROOFS.append("def Laws.%s():\n  {==}\n" % name)


def michael_laws():
    t, S, K = "Michael (IEEE 802.11i)", "Hs.HsMdState<Hs.HsW2>", "Hs.HsW2"
    U = lambda s, m: "MI.HsMichael.update(%s, %s)" % (s, m)
    F = lambda s: "MI.HsMichael.final(%s)" % s
    D = lambda m: "MI.HsMichael.mic(k, %s)" % m
    I = "MI.HsMichael.init(k)"
    LAWS.append("# Michael (michael.bend): the same laws, under every key\n")
    law("michael_streaming", "%s: update over a ++ b is update over a, then b, from every state" % t,
        ["s: %s" % S, "+a: B.Octets", "+b: B.Octets"], "{%s == %s : %s}" % (U("s", "B.Octets.append(a, b)"), U(U("s", "a"), "b"), S))
    PROOFS.append("def Laws.michael_streaming(s, a, b):\n  Laws.md_streaming(~Hs.HsW2, ~MI.HsMichael.compress, ~3, s, a, b)\n")
    law("michael_split", "%s: the tag in two pieces is the one-call tag, for every key and split" % t,
        ["+k: %s" % K, "+a: B.Octets", "+b: B.Octets"], "{%s == %s : B.Octets}" % (F(U(U(I, "a"), "b")), D("B.Octets.append(a, b)")))
    PROOFS.append("def Laws.michael_split(k, a, b):\n  %%Laws.michael_streaming(%s, a, b) : {%s == %s : B.Octets}\n  {==}\n"
                  % (I, F("_"), D("B.Octets.append(a, b)")))
    law("michael_length", "%s: the tag of every state has 8 bytes" % t, ["+s: %s" % S], "{B.Octets.len(%s) == 8n : Nat}" % F("s"))
    PROOFS.append("def Laws.michael_length(s):\n  w2le_len(Hs.HsMd.cv(~Hs.HsW2, Hs.HsMd.update_list(~Hs.HsW2, ~MI.HsMichael.compress, ~3, s, "
                  "MI.hs.michael.pad(Hs.HsMd.count(~Hs.HsW2, s)))))\n")
    law("michael_mic_length", "%s: the tag of every message under every key has 8 bytes" % t, ["+k: %s" % K, "+m: B.Octets"],
        "{B.Octets.len(%s) == 8n : Nat}" % D("m"))
    PROOFS.append("def Laws.michael_mic_length(k, m):\n  Laws.michael_length(%s)\n" % U(I, "m"))
    R = "Result<&2, &2, Hs.HsError, Unit>"
    law("michael_short_key", "%s: a key of 7 bytes is refused" % t, [],
        "{Result.map(&2, &2, Hs.HsError, %s, Unit, k => Unit{}, MI.HsMichael.key(B.Octets.zeros(7n))) == Fail{Hs.HsBadKeyLength{7n}} : %s}" % (K, R))
    PROOFS.append("def Laws.michael_short_key():\n  {==}\n")
    for i, (k, m, v) in enumerate(model.MICHAEL_V, 1):
        res = "Result<&2, &2, Hs.HsError, B.Octets>"
        law("michael_vector_%d" % i, "%s: test vector %d as recalled from IEEE 802.11i's Annex H.2 (each key the previous tag), not checked against a published copy (README.md)" % (t, i), [],
            "{Result.map(&2, &2, Hs.HsError, %s, B.Octets, k => %s, MI.HsMichael.key(%s)) == Done{%s} : %s}"
            % (K, D(octets(m)), digest_lit(k), digest_lit(v), res))
        PROOFS.append("def Laws.michael_vector_%d():\n  {==}\n" % i)
    law("michael_tkip_m63", "%s: IEEE Std 802.11-2012, M.6.3 (the TKIP test vector, as hostap's BSD-licensed wlantest/test_vectors.c reproduces it): the MIC of its MSDU (DA, SA, priority 0 and three zero bytes, then the data) under TK bytes 16 to 23" % t, [],
        "{Result.map(&2, &2, Hs.HsError, %s, B.Octets, k => %s, MI.HsMichael.key(%s)) == Done{%s} : Result<&2, &2, Hs.HsError, B.Octets>}"
        % (K, D(octets(model.TKIP_M63_INPUT)), digest_lit(model.TKIP_M63_KEY.hex()), digest_lit(model.TKIP_M63_MIC)))
    PROOFS.append("def Laws.michael_tkip_m63():\n  {==}\n")


for h in HASHES:
    hash_laws(h)
streebog_laws()
michael_laws()


def files():
    laws = LAWS_HEAD + "\n" + "\n".join(LAWS)
    proofs = PROOF_HEAD + "\n" + "\n".join(LEN_LEMMAS) + "\n" + "\n".join(PROOFS)
    return [("LAWS.bend", laws), ("PROOF.bend", proofs)]


def main():
    check = "--check" in sys.argv[1:]
    stale = []
    for fname, body in files():
        path = os.path.join(PKG, fname)
        old = open(path).read() if os.path.exists(path) else None
        if old != body:
            stale.append(fname)
            if not check:
                with open(path, "w", newline="\n") as f:
                    f.write(body)
    if check:
        if stale:
            print("out of date (run gen/laws.py): " + ", ".join(stale))
            sys.exit(1)
        print("LAWS.bend and PROOF.bend up to date")


if __name__ == "__main__":
    main()
