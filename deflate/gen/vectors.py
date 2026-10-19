#!/usr/bin/env python3
"""Writes LAWS.bend's generated vectors and their proofs in PROOF.bend: the
streams of ref/gen.py's handmade() (each kind of malformed stream) and
streams zlib and gzip write, each with the answer Python's zlib module gives
(checked here; for gzip files the answers are the gzip tool's, which the
differential test checks). Run it from deflate/; it replaces the blocks
between the BEGIN and END marker lines of both files.
"""
import os, sys, zlib, gzip
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ref"))
import gen
hm = gen.handmade()
R = "Result<&2, &2, E.DeflateError, B.Octets>"

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def oct_(b):
    return "B.Octets.of_list(%s)" % lst(b) if b else "B.Octets.empty()"

out = []
def law(name, comment, body):
    out.append("# " + comment if comment else "")
    out.append("law %s:" % name)
    out.append("  " + body)
    out.append("")

def inf(name, comment, data, want, mx=1000, ignore=True, fn="I.inflate_with"):
    w = ("Done{%s}" % oct_(want)) if isinstance(want, bytes) else "Fail{E.%s{}}" % want
    law(name, comment, "{%s(I.InflateOptions{%d, B.Octets.empty(), %s}, %s) == %s : %s}" % (fn, mx, "True{}" if ignore else "False{}", oct_(data), w, R))

# check the expected answers with zlib first
def zl_ok(data, wbits):
    try:
        return zlib.decompress(data, wbits)
    except Exception:
        return None

vec = [
 ("inflate_stored", "a stored block (3.2.4): BFINAL 1, BTYPE 00, LEN 3, NLEN, the bytes", hm["stored"], b"abc"),
 ("inflate_stored_empty", "an empty final stored block", hm["stored_empty"], b""),
 ("inflate_fixed_empty", "zlib's raw stream for no data: one empty fixed block", bytes([3, 0]), b""),
 ("inflate_fixed_a", "zlib's raw stream for \"a\"", bytes([75, 4, 0]), b"a"),
 ("inflate_fixed_match", "zlib's raw stream for \"hello hello hello\" (a match reaching back 6 and overlapping itself)", bytes([203, 72, 205, 201, 201, 87, 200, 64, 144, 0]), b"hello hello hello"),
 ("inflate_dynamic", "a dynamic block (3.2.7) holding \"A\", its literal/length code two one-bit codes", hm["dyn_two"], b"A"),
 ("inflate_dynamic_four", "a dynamic block with a match at distance 1 (\"AAAA\")", hm["dyn_four"], b"AAAA"),
 ("inflate_dist_single", "one distance code of one bit (3.2.7), used", hm["dyn_dist_used_bit"], b"AAAA"),
 ("inflate_end_only", "a literal/length code of one one-bit code, 256", hm["dyn_end_only"], b""),
 ("refuse_btype", "BTYPE 11 (3.2.3: \"reserved (error)\")", hm["btype3"], "DeflateBadBlockType"),
 ("refuse_nlen", "NLEN not the one's complement of LEN (3.2.4)", hm["stored_badnlen"], "DeflateBadStoredLength"),
 ("refuse_cut", "a stored block cut short", hm["stored_short"], "DeflateTruncated"),
 ("refuse_nonfinal", "a stream with no final block", hm["stored_nonfinal"], "DeflateTruncated"),
 ("refuse_empty", "no input at all", b"", "DeflateTruncated"),
 ("refuse_lit286", "literal/length symbol 286 in a fixed block (3.2.6)", hm["fixed_286"], "DeflateBadLitLenSymbol"),
 ("refuse_dist30", "distance symbol 30 in a fixed block (3.2.6)", hm["fixed_dist30"], "DeflateBadDistSymbol"),
 ("refuse_far", "a distance past the start of the output (3.2.3)", hm["fixed_far"], "DeflateDistanceTooFar"),
 ("refuse_far_extra", "a distance past the start, by its extra bits", hm["fixed_far_extra"], "DeflateDistanceTooFar"),
 ("refuse_hlit", "HLIT 29 + 1: 287 literal/length codes", hm["dyn_hlit30"], "DeflateTooManyCodes"),
 ("refuse_hdist", "HDIST 30: 31 distance codes", hm["dyn_hdist30"], "DeflateTooManyCodes"),
 ("refuse_clen_incomplete", "an incomplete code length code", hm["dyn_clen_incomplete"], "DeflateBadCodeLengthCode"),
 ("refuse_clen_over", "an over-subscribed code length code", hm["dyn_clen_over"], "DeflateBadCodeLengthCode"),
 ("refuse_rep_first", "code 16 with no length before it", hm["dyn_rep16_first"], "DeflateBadRepeat"),
 ("refuse_rep_past", "a repeat past the HLIT + HDIST lengths", hm["dyn_rep_past"], "DeflateBadRepeat"),
 ("refuse_lit_incomplete", "an incomplete literal/length code", hm["dyn_lit_incomplete"], "DeflateBadLitLenCode"),
 ("refuse_lit_over", "an over-subscribed literal/length code", hm["dyn_lit_over"], "DeflateBadLitLenCode"),
 ("refuse_no_end", "a literal/length code with no code for 256", hm["dyn_no_end"], "DeflateNoEndCode"),
 ("refuse_dist_incomplete", "an incomplete distance code", hm["dyn_dist_incomplete"], "DeflateBadDistCode"),
 ("refuse_dist_over", "an over-subscribed distance code", hm["dyn_dist_over"], "DeflateBadDistCode"),
 ("refuse_dist_single2", "a single distance code of two bits", hm["dyn_dist_single2"], "DeflateBadDistCode"),
 ("refuse_lit_unused", "the unused code of a one-code literal/length code", hm["dyn_lit_unused_bit"], "DeflateBadLitLenSymbol"),
 ("refuse_dist_unused", "the unused code of a one-code distance code", hm["dyn_dist_unused_bit"], "DeflateBadDistSymbol"),
 ("refuse_dist_none", "a match in a block with no distance codes", hm["dyn_dist_none_used"], "DeflateBadDistSymbol"),
]
for name, comment, data, want in vec:
    z = zl_ok(data, -15)
    if want is None:
        want = z
    if isinstance(want, bytes):
        assert z == want, (name, z, want)
    else:
        assert z is None, (name, z)
    inf(name, comment, data, want)
inf("refuse_too_large", "more output than the maximum (3 bytes, maximum 2)", hm["stored"], "DeflateOutputTooLarge", mx=2)
inf("refuse_trailing", "bytes after the stream, when refused", hm["stored_trailing"], "DeflateTrailingData", ignore=False)
inf("ignore_trailing", "bytes after the stream, ignored (as zlib ignores them)", hm["stored_trailing"], b"abc")

# zlib
zg = zlib.compress(b"")
def zhdr(cmf, flevel=2, fdict=0):
    flg = (flevel << 6) | (fdict << 5)
    flg += (31 - (cmf * 256 + flg) % 31) % 31
    return bytes([cmf, flg])
zv = [
 ("zlib_empty", "zlib's stream for no data (RFC 1950, 2.2: CMF 0x78, FLG 0x9C, then ADLER32 1)", zg, b""),
 ("zlib_a", "zlib's stream for \"a\"", zlib.compress(b"a"), b"a"),
 ("zlib_refuse_fcheck", "CMF * 256 + FLG not a multiple of 31", bytes([0x78, 0x9D]) + zg[2:], "DeflateZlibBadHeader"),
 ("zlib_refuse_cm", "CM 7", zhdr(0x77) + zg[2:], "DeflateZlibBadMethod"),
 ("zlib_refuse_cinfo", "CINFO 8 (\"Values of CINFO above 7 are not allowed\")", zhdr(0x88) + zg[2:], "DeflateZlibBadWindow"),
 ("zlib_refuse_fdict", "FDICT set, and no dictionary", zhdr(0x78, 2, 1) + b"\0\0\0\1" + zg[2:], "DeflateZlibNeedDict"),
 ("zlib_refuse_adler", "an ADLER32 that is not the data's", zg[:-1] + bytes([zg[-1] ^ 1]), "DeflateZlibBadChecksum"),
 ("zlib_refuse_short", "ADLER32 cut short", zg[:-1], "DeflateTruncated"),
]
for name, comment, data, want in zv:
    z = zl_ok(data, 15)
    if isinstance(want, bytes):
        assert z == want, name
    else:
        assert z is None, name
    inf(name, comment, data, want, fn="Z.zlib_decompress_with")

gz0 = gzip.compress(b"", mtime=0)
gza = gzip.compress(b"a", mtime=0)
gv = [
 ("gzip_empty", "Python's gzip member for no data (RFC 1952, 2.3.1)", gz0, b""),
 ("gzip_a", "Python's gzip member for \"a\"", gza, b"a"),
 ("gzip_two", "two members, one after the other (2.2)", gza + gza, b"aa"),
 ("gzip_zeros", "a member, then zero bytes (ignored, as the gzip tool ignores them)", gza + bytes(4), b"a"),
 ("gzip_refuse_magic", "not ID1 ID2", b"\x1f\x8c" + gza[2:], "DeflateGzipBadMagic"),
 ("gzip_refuse_cm", "CM 7", gza[:2] + bytes([7]) + gza[3:], "DeflateGzipBadMethod"),
 ("gzip_refuse_flags", "a reserved FLG bit (\"Reserved FLG bits must be zero\")", gza[:3] + bytes([32]) + gza[4:], "DeflateGzipReservedFlags"),
 ("gzip_refuse_crc", "a CRC32 that is not the data's", gza[:-8] + bytes([gza[-8] ^ 1]) + gza[-7:], "DeflateGzipBadCrc"),
 ("gzip_refuse_size", "an ISIZE that is not the data's size", gza[:-1] + bytes([gza[-1] ^ 1]), "DeflateGzipBadSize"),
 ("gzip_refuse_hcrc", "an FHCRC that is not the header's", gza[:3] + bytes([2]) + gza[4:10] + b"\0\0" + gza[10:], "DeflateGzipBadHeaderCrc"),
 ("gzip_refuse_empty", "no input at all", b"", "DeflateTruncated"),
]
for name, comment, data, want in gv:
    inf(name, comment, data, want, fn="G.gzip_decompress_with")

names = [l.split()[1].rstrip(":") for l in out if l.startswith("law ")]
BEGIN = "# BEGIN generated by gen/vectors.py"
END = "# END generated by gen/vectors.py"


def splice(path, text):
    s = open(path).read()
    i = s.index(BEGIN)
    j = s.index(END) + len(END)
    with open(path, "w", newline="\n") as f:
        f.write(s[:i] + BEGIN + "\n\n" + text + "\n" + END + s[j:])


splice("LAWS.bend", "\n".join(out))
splice("PROOF.bend", "\n".join("def Laws.%s():\n  {==}\n" % n for n in names))
