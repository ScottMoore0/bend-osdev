#!/usr/bin/env python3
"""Prints the vector laws of ../LAWS.bend (or their proofs, for
../PROOF.bend). The streams are those logged in ../ref/OBSERVATIONS.md
(Linux's own output, or streams Linux was given, with Linux's answers) and
the paper's examples; expected values come from ../ref/model.py, and agree
with Linux's recorded answers.

    vectors.py laws | proofs
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "ref"))
import model

R = "Result<&2, &2, E.C842Error, B.Octets>"
NAMES = {"truncated": "C842Truncated", "too_large": "C842OutputTooLarge", "bad_template": "C842BadTemplate",
         "bad_pointer": "C842BadPointer", "bad_repeat": "C842BadRepeat", "bad_short": "C842BadShort",
         "bad_crc": "C842BadCrc"}

laws = []


def oct_(b):
    return "B.Octets.of_list([%s])" % ", ".join(str(x) for x in b)


def res(r):
    if r[0] == "ok":
        return "Done{%s}" % oct_(r[1])
    return "Fail{E.%s{}}" % NAMES[r[1]]


def law(name, comment, body):
    laws.append((name, comment, body))


def dec(name, comment, stream, cap):
    law(name, comment, "{D.c842.decompress(%s, %dn) == %s : %s}" % (oct_(stream), cap, res(model.decode(stream, cap)), R))


def cmp(name, comment, data, want):
    assert model.compress(data) == want, (name, model.compress(data).hex())
    law(name, comment, "{L.compress(%s) == %s : B.Octets}" % (oct_(data), oct_(want)))


def chunk(w, c):
    w.put(0, 5)
    for i in range(0, 8, 2):
        w.put(c[i] * 256 + c[i + 1], 16)


def output_of(w):
    """The model's output for the bits so far (as if the end came next)."""
    tmp = model.Writer()
    tmp.bits = list(w.bits)
    tmp.put(30, 5)
    tmp.put(0, 32)
    got = []
    orig = model.crc
    model.crc = lambda d: (got.append(bytes(d)), orig(d))[1]
    try:
        model.decode(tmp.pack())
    finally:
        model.crc = orig
    return got[0]


def end(w):
    w.put(30, 5)
    w.put(model.crc(output_of(w)), 32)
    return w.pack()


A, Bb = b"ABCDEFGH", b"abcdefgh"

# The paper (Blaner et al. 2013)
law("paper_z8_rpt63", "the paper's example, Z8 then RPT(63): 512 zero bytes in 5 + 5 + 6 bits\n# (RPT's field holds 62: 63 more chunks; E1); then the end, CRC 0",
    "{D.c842.decompress(B.Octets.of_list([230, 254, 240, 0, 0, 0, 0, 0]), 512n) == Done{B.Octets.zeros(512n)} : %s}" % R)
law("paper_z8_rpt63_bits", "those two codes are 16 bits",
    "{List.length(&2, Bool, F.c842.serialise([F.C842Zero{}, F.C842Repeat{62}])) == 16n : Nat}")
law("paper_p8_bits", "P8 and its 8-bit pointer: 13 bits for 8 bytes",
    "{List.length(&2, Bool, F.c842.fmt.token(F.C842Chunk{25, [F.C842Ptr{0}]})) == 13n : Nat}")
law("paper_p4_p2_ll", "the paper's P4_P2_LL: a 4-byte pointer, a 2-byte pointer, a literal\n# (the patent's state 22)",
    "{F.c842.template(22) == Some{[F.C842P4{}, F.C842P2{}, F.C842LL{}]} : Maybe<&2, List<&2, F.C842Kind>>}")
law("paper_max_69", "the most a chunk takes: 69 bits (a template and four literals)",
    "{List.length(&2, Bool, F.c842.fmt.token(F.C842Chunk{0, [F.C842Lit{1, 2}, F.C842Lit{3, 4}, F.C842Lit{5, 6}, F.C842Lit{7, 8}]})) == 69n : Nat}")
law("templates_26", "26 templates (the patent's Figure 3, states 0 to 25)",
    "{List.length(&2, List<&2, F.C842Kind>, F.c842.templates()) == 26n : Nat}")

# Linux's compressor (E1): the package writes the same streams
cmp("linux_ramp8", "Linux's streams (E1). 01 02 ... 08: template 0, the end, CRC 0x7D0F3681",
    bytes(range(1, 9)), bytes.fromhex("0008101820283038479f43cda0400000"))
cmp("linux_ramp1", "one byte: short data", b"\x01", bytes.fromhex("e901f02608edb800"))
cmp("linux_ramp9", "nine bytes: a chunk, then short data", bytes(range(1, 10)), bytes.fromhex("000810182028303847484fbf21ba8ec0"))
cmp("linux_zeros8", "eight zero bytes: Z8", bytes(8), bytes.fromhex("e780000000000000"))
cmp("linux_zeros24", "24 zero bytes: Z8, RPT(1)", bytes(24), bytes.fromhex("e6c1f00000000000"))
cmp("linux_repeat", "a chunk twice: RPT(0)", A * 2, bytes.fromhex("020a121a222a323a46c0f174ccca7000"))
cmp("linux_p4_ll_ll", "a 4-byte phrase seen before: template 20 (P4 LL LL), index 0",
    b"ABCDEFGHABCDwxyz", bytes.fromhex("020a121a222a323a45000eef0f2f5e212b0a400000000000"))
cmp("linux_p4_p4", "both halves seen: template 24 (P4 P4), indices 1 and 0",
    b"ABCDEFGHEFGHABCD", bytes.fromhex("020a121a222a323a4600200f3da0dfc98000000000000000"))
cmp("linux_p2", "2-byte phrases: template 11 (P2 LL LL P2), indices 0 and 3",
    b"ABCDEFGHABwxyzGH", bytes.fromhex("020a121a222a323a42c01dde1e5e80fd9494ab1e00000000"))
cmp("linux_p8", "a chunk seen two chunks back: template 25 (P8), index 0",
    A + Bb + A, bytes.fromhex("020a121a222a323a40185898d9195999da3201e91645bb90"))

# Linux's decoder (E2): every template of the patent's Figure 3, after two
# literal chunks, as Linux decoded it
for t in range(26):
    w = model.Writer()
    chunk(w, A)
    chunk(w, Bb)
    w.put(t, 5)
    k = 0
    for f in model.TEMPLATES[t]:
        if f == "LL":
            w.put(0x5152 + 0x101 * k, 16)
        elif f == "P2":
            w.put([1, 6, 3, 7][k % 4], 8)
        elif f == "P4":
            w.put([3, 1][k % 2], 9)
        else:
            w.put(1, 8)
        k += 1
    comment = "template %d (%s)" % (t, " ".join(model.TEMPLATES[t]))
    if t == 0:
        comment = "Linux's decoder (E2): each template after ABCDEFGH and abcdefgh as\n# literals. " + comment
    dec("linux_template%d" % t, comment, end(w), 24)

# Linux's answers to malformed streams (E2, E4, E7, E8)
ramp8 = bytes.fromhex("0008101820283038479f43cda0400000")
s = bytearray(ramp8)
s[10] ^= 1
dec("linux_bad_crc", "a flipped CRC bit: EINVAL", bytes(s), 100)
dec("linux_cut", "cut inside the CRC: EOVERFLOW", ramp8[:12], 100)
dec("linux_no_room", "16 bytes into 15: ENOSPC", model.literals(A + Bb), 15)
dec("linux_trailing", "bytes after the stream are ignored", ramp8 + b"\x05\x06", 100)
w = model.Writer()
chunk(w, A)
w.put(25, 5)
w.put(1, 8)
w.put(30, 5)
w.put(model.crc(A + A), 32)
dec("linux_unwritten", "P8 index 1 after one chunk: nothing written there yet, EINVAL", w.pack(), 100)
w = model.Writer()
w.put(29, 5)
w.put(3, 3)
w.put(0x616263, 24)
chunk(w, A)
dec("linux_short_mid", "short data before a chunk: accepted, the output carries on", end(w), 100)
dec("repeat_after_short", "RPT after 3 bytes, which Linux reads before its buffer (E8): refused",
    bytes.fromhex("eb616263d81e00000000000000000000"), 100)
law("crc_check", "the CRC's check value (of 123456789): 0x89A1897F",
    "{K.c842.crc(B.Octets.of_string(\"123456789\")) == 2309065087 : U32}")
law("worst_8", "the worst case for 8 bytes: 106 bits",
    "{F.c842.worst_bits(8n) == 106n : Nat}")
law("worst_64", "for 64 bytes: 589 bits, in 80 bytes (Linux wrote 80 for 64 random bytes, E1)",
    "{F.c842.worst_bytes(64n) == 80n : Nat}")
law("tokens_short", "the format's parser: one byte is short data, then the end",
    "{F.c842.tokens(B.Octets.of_list([233, 1, 240, 38, 8, 237, 184, 0])) == Done{[F.C842Short{[1]}, F.C842End{79764919}]} : Result<&2, &2, E.C842Error, List<&2, F.C842Token>>}")

if sys.argv[1] == "laws":
    for name, comment, body in laws:
        print("# " + comment)
        print("law %s:" % name)
        print("  " + body)
        print()
else:
    for name, comment, body in laws:
        print("def Laws.%s():" % name)
        print("  {==}")
        print()
