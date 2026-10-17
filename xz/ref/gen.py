#!/usr/bin/env python3
"""Differential test cases for bend-osdev-xz.

Writes ref/casesNN.bend (Bend programs that decode each case and print
"<k> ok <length> <sha256>" or "<k> error") and ref/expected.txt (the same,
from implementations outside this repository):

  * .xz files from Python's lzma module (presets 0 to 9 with each check type,
    the delta filter, an unsupported BCJ filter) and from the xz tool
    (presets, extreme mode, small block sizes, sizes in the block headers);
  * empty input, one byte, text, random and repetitive data;
  * concatenated streams, with and without stream padding;
  * raw LZMA2 streams spliced from several encoder runs, so that one stream
    has several chunks (dictionary resets, uncompressed chunks);
  * the same files corrupted in random places (a byte changed) and
    truncated, whose expected result comes from the xz tool (`xz -dc`):
    either an error, or the same output.

The expected output of an intact file is its original data, checked against
the xz tool (and Python's lzma.decompress, for the files it made); x86 BCJ
is expected to fail, since this package does not implement it. Sizes stay small (a few KB): byte strings are
slow, and deep lists overflow the runtime's stack, until faster storage
lands in bend-osdev-bytes.
"""
import hashlib, lzma, os, random, subprocess, sys

def words(rng, n):
    vocab = ("the of and to in is was that for on as with by he at from his it "
             "an were are which this be or has had first one their its new after "
             "who they two her she been other when there all during into school "
             "time may years more most only over city some world would where later "
             "up such used many can state about national out known university").split()
    return " ".join(rng.choice(vocab) for _ in range(n)).encode()

def xz_tool(data, args):
    return subprocess.run(["xz", "-z", "-c", "-q"] + args, input=data, stdout=subprocess.PIPE, check=True).stdout

def xz_verdict(blob):
    p = subprocess.run(["xz", "-d", "-c", "-q", "-q"], input=blob, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return p.stdout if p.returncode == 0 else None

def octets(blob):
    # the checker expands a literal recursively, so long ones go in pieces
    pieces = [blob[i:i + 256] for i in range(0, len(blob), 256)] or [b""]
    return "B.Octets.concat([" + ", ".join("B.Octets.of_list([%s])" % ", ".join(map(str, p)) for p in pieces) + "])"

def show(data):
    return "ok %d %s" % (len(data), hashlib.sha256(data).hexdigest()) if data is not None else "error"

CHECKS = [("none", lzma.CHECK_NONE), ("crc32", lzma.CHECK_CRC32), ("crc64", lzma.CHECK_CRC64), ("sha256", lzma.CHECK_SHA256)]

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    text = words(rng, 500)
    data = {
        "empty": b"",
        "one": b"x",
        "text": text,
        "random": bytes(rng.randrange(256) for _ in range(1200)),
        "repeat": b"bend-osdev " * 600,
        "lowent": bytes(rng.choice(b"ab\n") for _ in range(8000)),
        "long": words(rng, 2400),
    }
    xzs = []  # (name, .xz bytes, expected data or None)
    for p in range(10):
        for cname, check in CHECKS:
            xzs.append(("py-p%d-%s" % (p, cname), lzma.compress(text, format=lzma.FORMAT_XZ, check=check, preset=p), text))
    for name, d in data.items():
        for cname, check in CHECKS:
            xzs.append(("py-%s-%s" % (name, cname), lzma.compress(d, format=lzma.FORMAT_XZ, check=check), d))
    for dist in (1, 4, 256):
        f = [{"id": lzma.FILTER_DELTA, "dist": dist}, {"id": lzma.FILTER_LZMA2, "preset": 6}]
        xzs.append(("py-delta%d" % dist, lzma.compress(data["lowent"][:3000], format=lzma.FORMAT_XZ, filters=f), data["lowent"][:3000]))
    f = [{"id": lzma.FILTER_DELTA, "dist": 2}, {"id": lzma.FILTER_DELTA, "dist": 3}, {"id": lzma.FILTER_LZMA2, "preset": 1}]
    xzs.append(("py-delta2x", lzma.compress(text, format=lzma.FORMAT_XZ, filters=f), text))
    f = [{"id": lzma.FILTER_X86}, {"id": lzma.FILTER_LZMA2, "preset": 1}]
    xzs.append(("py-x86-unsupported", lzma.compress(text, format=lzma.FORMAT_XZ, filters=f), None))
    for lc, lp, pb in ((0, 0, 0), (4, 0, 4), (0, 4, 2), (1, 3, 0)):
        f = [{"id": lzma.FILTER_LZMA2, "preset": 6, "lc": lc, "lp": lp, "pb": pb}]
        xzs.append(("py-lc%dlp%dpb%d" % (lc, lp, pb), lzma.compress(data["long"], format=lzma.FORMAT_XZ, filters=f), data["long"]))
    for args in (["-0"], ["-1", "-C", "crc32"], ["-6", "-C", "sha256"], ["-9", "-C", "none"], ["-6e"], ["-3", "--block-size=1000"],
                 ["-6", "--block-size=4096", "-C", "crc32"], ["-T2", "--block-size=2000"], ["-1", "--check=crc64", "--block-size=500"]):
        for name in ("empty", "one", "long"):
            xzs.append(("xz%s-%s" % ("".join(args), name), xz_tool(data[name], args), data[name]))
    a = lzma.compress(b"first stream, ", format=lzma.FORMAT_XZ)
    b = xz_tool(b"second stream", ["-1", "-C", "crc32"])
    xzs.append(("concat", a + b, b"first stream, second stream"))
    xzs.append(("concat-pad", a + bytes(4) + b + bytes(8), b"first stream, second stream"))
    xzs.append(("concat-empty", lzma.compress(b"", format=lzma.FORMAT_XZ) + a, b"first stream, "))
    xzs.append(("concat-badpad", a + bytes(3) + b, None))
    xzs.append(("trailing-garbage", a + b"junk", None))
    xzs.append(("empty-input", b"", None))
    for name, blob, want in xzs:
        if want is not None and name.startswith("py-"):
            assert lzma.decompress(blob) == want, name
        if "unsupported" not in name:
            assert xz_verdict(blob) == want, name
    # corruptions, judged by the xz tool
    damaged = []
    sources = [x for x in xzs if x[2] is not None and "none" not in x[0] and x[1]]
    for k in range(60):
        name, blob, want = rng.choice(sources)
        bad = bytearray(blob)
        i = rng.randrange(len(bad))
        bad[i] ^= rng.randrange(1, 256)
        damaged.append(("%s-flip%d@%d" % (name, k, i), bytes(bad), xz_verdict(bytes(bad))))
    for k in range(20):
        name, blob, want = rng.choice(sources)
        n = rng.randrange(len(blob))
        damaged.append(("%s-cut%d@%d" % (name, k, n), blob[:n], xz_verdict(blob[:n])))
    cases = xzs + damaged
    # raw LZMA2 streams spliced from several encoder runs
    raws = []
    def raw(d, **kw):
        return lzma.compress(d, format=lzma.FORMAT_RAW, filters=[dict(id=lzma.FILTER_LZMA2, **kw)])[:-1]  # without the end marker
    parts = [data["text"][:900], data["repeat"][:700], data["random"][:300]]
    spliced = raw(parts[0], preset=6) + raw(parts[1], preset=1) + raw(parts[2], preset=9)
    raws.append(("raw-3runs", spliced + b"\0", b"".join(parts)))
    plain = b"stored as it is "
    unc = bytes([2, 0, len(plain) - 1]) + plain
    raws.append(("raw-uncompressed-mid", raw(parts[0], preset=6) + unc + raw(parts[1], preset=6) + b"\0", parts[0] + plain + parts[1]))
    raws.append(("raw-uncompressed-first", bytes([1, 0, len(plain) - 1]) + plain + raw(parts[1], preset=3) + b"\0", plain + parts[1]))
    raws.append(("raw-no-reset-first", unc + b"\0", None))
    raws.append(("raw-bad-control", bytes([3]) + b"\0", None))
    raws.append(("raw-trailing", raw(b"abc", preset=0) + b"\0" + b"x", None))
    raws.append(("raw-unended", raw(b"abc", preset=0), None))
    raws.append(("raw-random", lzma.compress(parts[2], format=lzma.FORMAT_RAW, filters=[{"id": lzma.FILTER_LZMA2}]), parts[2]))
    for k in range(12):
        d = rng.choice(parts)
        blob = bytearray(raw(d, preset=rng.choice((0, 6))) + b"\0")
        blob[rng.randrange(1, len(blob))] ^= rng.randrange(1, 256)
        try:
            dec = lzma.LZMADecompressor(format=lzma.FORMAT_RAW, filters=[{"id": lzma.FILTER_LZMA2, "dict_size": 1 << 20}])
            out = dec.decompress(bytes(blob))
            want = out if dec.eof and not dec.unused_data else None
        except lzma.LZMAError:
            want = None
        raws.append(("raw-flip%d" % k, bytes(blob), want))
    # streaming: intact files fed to XzDecoder (and raw streams to XzLzma2)
    # in pieces of random sizes
    streams = []
    for k in range(16):
        name, blob, want = rng.choice([x for x in xzs if x[2] is not None])
        cuts = sorted(rng.sample(range(1, len(blob)), min(len(blob) - 1, rng.randrange(1, 40)))) if len(blob) > 1 else []
        pieces = [blob[i:j] for i, j in zip([0] + cuts, cuts + [len(blob)])]
        streams.append(("stream-%s" % name, "xz", pieces, want))
    for name, blob, want in raws[:3]:
        cuts = sorted(rng.sample(range(1, len(blob)), 25))
        streams.append(("stream-%s" % name, "raw", [blob[i:j] for i, j in zip([0] + cuts, cuts + [len(blob)])], want))
    lines, expect = [], []
    def case(name, call, want):
        k = len(lines)
        lines.append('    IO.print("%d %s " ++ xzref_show(%s))' % (k, name, call))
        expect.append("%d %s %s" % (k, name, show(want)))
    for name, blob, want in cases:
        case(name, "X.xz_decode(X.XzParams{1048576}, %s)" % octets(blob), want)
    for name, blob, want in raws:
        case(name, "L2.XzLzma2.decode(1048576, 1048576, %s)" % octets(blob), want)
    for name, kind, pieces, want in streams:
        ps = "[" + ", ".join(octets(p) for p in pieces) + "]"
        if kind == "xz":
            case(name, "xzref_feed_xz(%s, Done{X.XzFed{X.XzDecoder.start(X.XzParams{1048576}), B.Octets.empty()}}, B.Octets.empty())" % ps, want)
        else:
            case(name, "xzref_feed_l2(%s, Done{L2.XzLzma2Fed{L2.XzLzma2.start(1048576, 1048576), B.Octets.empty(), False{}}}, B.Octets.empty())" % ps, want)
    header = """import Base
import ../../bytes/bytes.bend as B
import ../error.bend as E
import ../lzma2.bend as L2
import ../xz.bend as X
import bend-collections@1.0.0.0/src/crypto/sha/sha256.bend as Sha

def xzref_show(r: Result<&2, &2, E.XzError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "error"
    case Done{+o}:
      "ok " ++ Nat.show(B.Octets.len(o)) ++ " " ++ B.hex(Sha.sha256_bytes(B.Octets.to_list(o)))

def xzref_join(r: Result<&2, &2, E.XzError, B.Octets>, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{B.Octets.append(acc, o)}

# the pieces ps fed one at a time; r is the last feed's answer
def xzref_feed_xz(ps: List<&2, B.Octets>, r: Result<&2, &1, E.XzError, X.XzFed>, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match ps:
    case Nil{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{X.XzFed{d, out}}:
          xzref_join(X.XzDecoder.finish(d), B.Octets.append(acc, out))
    case Con{p, t}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{X.XzFed{d, out}}:
          xzref_feed_xz(t, X.XzDecoder.feed(d, p), B.Octets.append(acc, out))

def xzref_none_left(n: Nat, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match n:
    case 0n:
      Done{acc}
    case 1n+k:
      Fail{E.XzTrailingData{}}

def xzref_end_l2(r: Result<&2, &2, E.XzError, L2.XzLzma2End>, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{L2.XzLzma2End{rest, n, room}}:
      xzref_none_left(B.Octets.len(rest), acc)

def xzref_feed_l2(ps: List<&2, B.Octets>, r: Result<&2, &1, E.XzError, L2.XzLzma2Fed>, acc: B.Octets) -> Result<&2, &2, E.XzError, B.Octets>:
  match ps:
    case Nil{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{L2.XzLzma2Fed{d, out, ended}}:
          xzref_end_l2(L2.XzLzma2.finish(d), B.Octets.append(acc, out))
    case Con{p, t}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{L2.XzLzma2Fed{d, out, ended}}:
          xzref_feed_l2(t, L2.XzLzma2.feed(d, p), B.Octets.append(acc, out))

def main() -> IO(Unit):
  do IO<Unit>:
"""
    # the checker's memory grows with a file's literals, so the cases go in
    # files of about 150 KB each
    for old in os.listdir(here):
        if old.startswith("cases") and old.endswith(".bend"):
            os.remove(os.path.join(here, old))
    files, cur, size = [], [], 0
    for line in lines:
        if cur and size + len(line) > 150000:
            files.append(cur)
            cur, size = [], 0
        cur.append(line)
        size += len(line)
    files.append(cur)
    for n, part in enumerate(files):
        with open(os.path.join(here, "cases%02d.bend" % n), "w") as f:
            f.write(header + "\n".join(part) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
