#!/usr/bin/env python3
"""The block ciphers cipher-modes runs over, and the laws written per cipher.

  python3 gen/instances.py           rewrite LAWS.bend, PROOF.bend and check.bend
  python3 gen/instances.py --check   only check that they are up to date

cipher-modes states its four round-trip laws (cbc_blocks_round_trip,
cbc_round_trip, xts_blocks_round_trip, xts_round_trip) once, for every
cipher, with the hypothesis inv: for every list of blocks xs,
CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs, at the law's key. That
hypothesis is an ordinary one, used once, which --verdict models. For a
cipher whose own package proves dec(k, enc(k, b)) == b for every key and
block, this script writes:

  * <c>_dec_enc: the cipher meets the hypothesis at every key (an induction
    on xs that uses the cipher's law at every block: a global law may be used
    any number of times);
  * <c>_cbc_blocks_round_trip, <c>_cbc_round_trip, <c>_xts_blocks_round_trip,
    <c>_xts_round_trip: cipher-modes' laws at the cipher's template
    arguments, each proved by cipher-modes' law with <c>_dec_enc as inv.

Adding a cipher: a row in CIPHERS (its import, its key type, its encryption
and decryption, the law of its package that decryption undoes encryption,
and a key the cipher accepts for check.bend), then run this script.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..")


def row(name, title, alias, path, K, key, enc, dec, rt, tkey):
    return dict(name=name, title=title, alias=alias, path=path, K=K, key=key, enc=enc, dec=dec, rt=rt, tkey=tkey)


K16 = "000102030405060708090a0b0c0d0e0f"
CIPHERS = [
    row("sm4", "SM4 (legacy-ciphers)", "S", "../legacy-ciphers/sm4.bend", "S.LcSm4Key", "S.LcSm4.key",
        "S.LcSm4.encrypt", "S.LcSm4.decrypt", "LL.sm4_round_trip", K16),
    row("camellia", "Camellia (legacy-ciphers)", "Ca", "../legacy-ciphers/camellia.bend", "Ca.LcCamelliaKey", "Ca.LcCamellia.key",
        "Ca.LcCamellia.encrypt", "Ca.LcCamellia.decrypt", "LL.camellia_round_trip", K16),
    row("serpent", "Serpent (legacy-ciphers)", "Sp", "../legacy-ciphers/serpent.bend", "Sp.LcSerpentKey", "Sp.LcSerpent.key",
        "Sp.LcSerpent.encrypt", "Sp.LcSerpent.decrypt", "LL.serpent_round_trip", K16),
    row("twofish", "Twofish (legacy-ciphers)", "Tf", "../legacy-ciphers/twofish.bend", "Tf.LcTwofishKey", "Tf.LcTwofish.key",
        "Tf.LcTwofish.encrypt", "Tf.LcTwofish.decrypt", "LL.twofish_round_trip", K16),
    row("aria", "ARIA (legacy-ciphers)", "Ar", "../legacy-ciphers/aria.bend", "Ar.LcAriaKey", "Ar.LcAria.key",
        "Ar.LcAria.encrypt", "Ar.LcAria.decrypt", "LL.aria_round_trip", K16),
    row("cast6", "CAST-256 (legacy-ciphers)", "C6", "../legacy-ciphers/cast6.bend", "C6.LcCast6Key", "C6.LcCast6.key",
        "C6.LcCast6.encrypt", "C6.LcCast6.decrypt", "LL.cast6_round_trip", K16),
]

L = "List<&2, M.CmBlock>"
R = "Result<&2, &2, M.CmError, B.Octets>"


def tpl(c):
    return "~%s, ~%s, ~%s" % (c["K"], c["enc"], c["dec"])


def laws_of(c):
    K, enc, dec, t = c["K"], c["enc"], c["dec"], c["title"]
    out = ["# %s\n" % t]
    out.append("# meets cipher-modes' round-trip hypothesis at every key\n"
               "law %s_dec_enc:\n  for +k: %s\n  for xs: %s\n  {M.CmBlock.dec_enc(%s, k, xs) == xs : %s}\n"
               % (c["name"], K, L, tpl(c), L))
    out.append("law %s_cbc_blocks_round_trip:\n  for +k: %s\n  for iv: M.CmBlock\n  for bs: %s\n"
               "  {CB.Cbc.decrypt_blocks(~%s, ~%s, k, iv, CB.Cbc.encrypt_blocks(~%s, ~%s, k, iv, bs)) == bs : %s}\n"
               % (c["name"], K, L, K, dec, K, enc, L))
    out.append("law %s_cbc_round_trip:\n  for +k: %s\n  for +iv: B.Octets\n  for +m: B.Octets\n"
               "  for hi: {B.Octets.len(iv) == 16n : Nat}\n  for hm: {Nat.mod(B.Octets.len(m), 16n) == 0n : Nat}\n"
               "  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~%s, ~%s, k, iv, m), c => CB.Cbc.decrypt(~%s, ~%s, k, iv, c)) == Done{m} : %s}\n"
               % (c["name"], K, K, enc, K, dec, R))
    out.append("law %s_xts_blocks_round_trip:\n  for +k1: %s\n  for t: M.CmBlock\n  for bs: %s\n"
               "  {XT.Xts.decrypt_blocks(~%s, ~%s, k1, t, XT.Xts.encrypt_blocks(~%s, ~%s, k1, t, bs)) == bs : %s}\n"
               % (c["name"], K, L, K, dec, K, enc, L))
    out.append("law %s_xts_round_trip:\n  for +k1: %s\n  for +k2: %s\n  for +i: B.Octets\n  for +p: B.Octets\n"
               "  for hi: {B.Octets.len(i) == 16n : Nat}\n  for hp: {Nat.is_le(16n, B.Octets.len(p)) == True{} : Bool}\n"
               "  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~%s, ~%s, k1, k2, i, p), c => XT.Xts.decrypt(~%s, ~%s, ~%s, k1, k2, i, c)) == Done{p} : %s}\n"
               % (c["name"], K, K, K, enc, K, enc, dec, R))
    return "\n".join(out)


def proofs_of(c):
    n, enc, dec = c["name"], c["enc"], c["dec"]
    DE = lambda xs: "M.CmBlock.dec_enc(%s, k, %s)" % (tpl(c), xs)
    inv = "xs => Laws.%s_dec_enc(%s, xs)"
    out = ["# %s\n" % c["title"]]
    out.append("def Laws.%s_dec_enc(k, xs):\n"
               "  match xs:\n"
               "    case Nil{}:\n"
               "      {==}\n"
               "    case Con{+x, +t}:\n"
               "      %%Equal.sym(M.CmBlock, %s(k, %s(k, x)), x, %s(k, x)) : {Con{_, %s} == Con{x, t} : %s}\n"
               "      %%Equal.sym(%s, %s, t, Laws.%s_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : %s}\n"
               "      {==}\n" % (n, dec, enc, c["rt"], DE("t"), L, L, DE("t"), n, L))
    out.append("def Laws.%s_cbc_blocks_round_trip(k, iv, bs):\n  CML.cbc_blocks_round_trip(%s, k, %s, iv, bs)\n"
               % (n, tpl(c), inv % (n, "k")))
    out.append("def Laws.%s_cbc_round_trip(k, iv, m, hi, hm):\n  CML.cbc_round_trip(%s, k, %s, iv, m, hi, hm)\n"
               % (n, tpl(c), inv % (n, "k")))
    out.append("def Laws.%s_xts_blocks_round_trip(k1, t, bs):\n  CML.xts_blocks_round_trip(%s, k1, %s, t, bs)\n"
               % (n, tpl(c), inv % (n, "k1")))
    out.append("def Laws.%s_xts_round_trip(k1, k2, i, p, hi, hp):\n  CML.xts_round_trip(%s, k1, k2, %s, i, p, hi, hp)\n"
               % (n, tpl(c), inv % (n, "k1")))
    return "\n".join(out)


def imports():
    return "".join("import %s as %s\n" % (c["path"], c["alias"]) for c in CIPHERS)


LAWS_HEAD = '''# Laws of cipher-modes' modes over each block cipher it runs over, written
# out per cipher by gen/instances.py (do not edit by hand: change the script
# and run it).
#
# For each cipher c: c_dec_enc, the cipher meets cipher-modes' round-trip
# hypothesis (CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs) at every key and
# list of blocks; and cipher-modes' four round-trip laws at c's template
# arguments, with no hypothesis: CBC on blocks for every key, IV and list of
# blocks; CBC on bytes for every key, 16-byte IV and message of whole blocks;
# XTS on blocks for every data key and starting tweak; XTS on bytes, with
# ciphertext stealing, for every pair of keys, 16-byte sequence number and
# data unit of at least 16 bytes.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cbc.bend as CB
import ../cipher-modes/xts.bend as XT
'''

PROOF_HEAD = '''# Proofs of LAWS.bend, written by gen/instances.py: each c_dec_enc by
# induction on the list, with the cipher's own round-trip law (legacy-ciphers'
# LAWS.bend) at every block; each mode law is cipher-modes' law at the
# cipher's template arguments, with c_dec_enc as its hypothesis.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cbc.bend as CB
import ../cipher-modes/xts.bend as XT
import ../cipher-modes/LAWS.bend as CML
import ../cipher-modes/PROOF.bend as CMP
'''


def laws_file():
    return (LAWS_HEAD + imports() + "\n" + "\n".join(laws_of(c) for c in CIPHERS))


def proof_file():
    return (PROOF_HEAD + imports() + "import ../legacy-ciphers/LAWS.bend as LL\nimport ../legacy-ciphers/PROOF.bend as LP\n"
            + "import ./LAWS.bend as Laws\n\n" + "\n".join(proofs_of(c) for c in CIPHERS))


CHECK_HEAD = '''# Every cipher through cipher-modes' four round trips, at run time: a key
# the cipher accepts, a 16-byte IV or sequence number, and data of 64 bytes
# (CBC, and XTS on whole blocks) and 61 bytes (XTS with ciphertext
# stealing), encrypted and decrypted back. Written by gen/instances.py. The
# ciphers' own values are tested in legacy-ciphers (its vectors, and CBC
# against cryptography and the openssl command), the modes' in cipher-modes.
import Base
import ../bytes/bytes.bend as B
import ../legacy-ciphers/legacy-ciphers.bend as LC
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cbc.bend as CB
import ../cipher-modes/xts.bend as XT
'''

CHECK_DEFS = '''
def hx.digit(+c: U32) -> U32:
  U32.sub(c, U32.add(48, U32.mul(39, U32.shrn(c, 6n))))

def hx.go(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Con{a, Con{b, t}}:
      hx.go(t, Con{U32.or(U32.shln(hx.digit(a), 4n), hx.digit(b)), acc})
    case _:
      List.reverse(&2, U32, acc)

def hx(s: String) -> B.Octets:
  B.Octets.of_list(hx.go(B.Octets.to_list(B.Octets.of_string(s)), Nil{}))

# n bytes 0, 1, 2, ...
def seq.go(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      seq.go(p, U32.add(i, 1), Con{U32.and(255, i), acc})

def seq(n: Nat) -> B.Octets:
  B.Octets.of_list(seq.go(n, 0, Nil{}))

def ok(b: Bool) -> String:
  match b:
    case True{}:
      "ok"
    case False{}:
      "FAIL"

def same(r: Result<&2, &2, M.CmError, B.Octets>, +m: B.Octets) -> String:
  match r:
    case Done{x}:
      ok(B.Octets.is_eq(x, m))
    case Fail{e}:
      "FAIL"

def blocks() -> List<&2, M.CmBlock>:
  [M.CmBlock{1, 2, 3, 4}, M.CmBlock{5, 6, 7, 8}, M.CmBlock{9, 10, 11, 12}, M.CmBlock{13, 14, 15, 16}]

def tw() -> M.CmBlock:
  M.CmBlock{1, 2, 3, 4}

def same_blocks(xs: List<&2, M.CmBlock>, ys: List<&2, M.CmBlock>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(B.Octets.is_eq(M.CmBlock.to_octets(x), M.CmBlock.to_octets(y)), same_blocks(xt, yt))
    case _ _:
      False{}

# the four round trips under k (k2 the XTS tweak key)
def four(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +name: String, +k: K, +k2: K) -> String:
  +iv = seq(16n)
  +m = seq(64n)
  +p = seq(61n)
  +bs = blocks()
  +t = tw()
  name ++ " cbc_blocks " ++ ok(same_blocks(CB.Cbc.decrypt_blocks(~K, ~dec, k, t, CB.Cbc.encrypt_blocks(~K, ~enc, k, t, bs)), bs))
    ++ ", cbc " ++ same(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~K, ~enc, k, iv, m), c => CB.Cbc.decrypt(~K, ~dec, k, iv, c)), m)
    ++ ", xts_blocks " ++ ok(same_blocks(XT.Xts.decrypt_blocks(~K, ~dec, k, t, XT.Xts.encrypt_blocks(~K, ~enc, k, t, bs)), bs))
    ++ ", xts " ++ same(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~K, ~enc, k, k2, iv, m), c => XT.Xts.decrypt(~K, ~enc, ~dec, k, k2, iv, c)), m)
    ++ ", xts stealing " ++ same(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~K, ~enc, k, k2, iv, p), c => XT.Xts.decrypt(~K, ~enc, ~dec, k, k2, iv, c)), p)
'''


def check_case(c):
    K = c["K"]
    return ('''
def run.%s(a: Result<&2, &2, LC.LcError, %s>, b: Result<&2, &2, LC.LcError, %s>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~%s, ~%s, ~%s, "%s", k, k2)
    case _ _:
      "%s: key refused"
''' % (c["name"], K, K, K, c["enc"], c["dec"], c["name"], c["name"]))


def check_file():
    lines = [CHECK_HEAD, imports(), CHECK_DEFS]
    lines += [check_case(c) for c in CIPHERS]
    body = "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n"
    for c in CIPHERS:
        body += '    IO.print(run.%s(%s(hx("%s")), %s(hx("%s"))))\n' % (c["name"], c["key"], c["tkey"], c["key"], c["tkey"][::-1])
    lines.append(body)
    exp = "".join("#|%s cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok\n" % c["name"] for c in CIPHERS)
    return "".join(lines) + "\n" + exp


def main():
    files = {"LAWS.bend": laws_file(), "PROOF.bend": proof_file(), "check.bend": check_file()}
    stale = []
    for name, text in files.items():
        path = os.path.join(PKG, name)
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if old != text:
            stale.append(name)
            if "--check" not in sys.argv:
                with open(path, "w", encoding="utf-8", newline="\n") as f:
                    f.write(text)
    if "--check" in sys.argv:
        if stale:
            print("out of date: " + ", ".join(stale))
            sys.exit(1)
        print("up to date")
    else:
        print("wrote " + (", ".join(stale) if stale else "nothing (up to date)"))


main()
