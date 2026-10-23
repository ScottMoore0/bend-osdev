#!/usr/bin/env python3
"""Writes siphash/check.bend: every published vector of the reference
implementation's vectors.h (ref/vectors.py) through SipHash and HalfSipHash,
and the other cases below, with the expected output as #| lines.

  python3 gen/check.py           rewrite check.bend
  python3 gen/check.py --check   only check that it is up to date

Values not in vectors.h are the openssl command's (`openssl mac -macopt
hexkey:<key> -macopt size:<n> -macopt c-rounds:<c> -macopt d-rounds:<d>
SIPHASH`, OpenSSL 3.0.13), checked here against ref/model.py, or, for
HalfSipHash-1-3, which openssl lacks, ref/model.py's alone.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.join(HERE, "..")
sys.path.insert(0, os.path.join(PKG, "ref"))
from vectors import SIP64, SIP128, HSIP32, HSIP64  # noqa: E402
from model import siphash, halfsiphash  # noqa: E402

KEY = bytes(range(16))


def lcg(n, s=7):
    """n pseudo-random bytes, as check.bend's bulk builds them"""
    out = []
    for _ in range(n):
        s = (s * 1103515245 + 12345) & 0xFFFFFFFF
        out.append((s >> 16) & 255)
    return bytes(reversed(out))


# (label, the Bend expression, the expected hex, its source)
OPENSSL = [
    ("sip13 15", "S.siphash13(key16(), msg(15n))", "5699512a6dd820d3"),
    ("sip48 15", "S.SipHash.hash(S.SipParams.sip48(), key16(), msg(15n))", "e0a6a97dd589d383"),
    ("sip13 63", "S.siphash13(key16(), msg(63n))", "a8b3bbb76290199d"),
    ("sip24 bulk", "S.siphash24(key16(), bulk(10000n))", "9f3f57d2e8cedb67"),
]
MODEL = [
    ("hsip13 15", "H.halfsiphash13(key8(), msg(15n))", halfsiphash(KEY, bytes(range(15)), 1, 3).hex()),
    ("hsip13 63", "H.halfsiphash13(key8(), msg(63n))", halfsiphash(KEY, bytes(range(63)), 1, 3).hex()),
]


def check_openssl():
    want = {
        "sip13 15": siphash(KEY, bytes(range(15)), 1, 3),
        "sip48 15": siphash(KEY, bytes(range(15)), 4, 8),
        "sip13 63": siphash(KEY, bytes(range(63)), 1, 3),
        "sip24 bulk": siphash(KEY, lcg(10000)),
    }
    for label, _, hexv in OPENSSL:
        assert want[label].hex() == hexv, label


HEAD = '''# bend-osdev-siphash: the published vectors (vectors.h of the reference
# implementation, github.com/veorq/SipHash: the key 00 01 .. 0f, HalfSipHash
# its first 8 bytes, and the messages 00 01 .. (i - 1) for i = 0 to 63),
# then values of the openssl command and pieces, bytes and refusals.
# Written by gen/check.py; do not edit by hand.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./siphash.bend as S
import ./halfsiphash.bend as H

# the bytes 0, 1, .., n - 1
def iota.go(+n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      iota.go(p, Con{U32.from_nat(p), acc})

def msg(n: Nat) -> B.Octets:
  B.Octets.of_list(iota.go(n, Nil{}))

# n pseudo-random bytes (a linear congruential generator)
def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def bulk(n: Nat) -> B.Octets:
  B.Octets.of_list(bulk.go(n, 7, Nil{}))

def key16.of(r: Result<&2, &2, S.SipError, S.SipKey>) -> S.SipKey:
  match r:
    case Done{k}:
      k
    case Fail{e}:
      S.SipKey.of_words(W.W64.zero(), W.W64.zero())

def key16() -> S.SipKey:
  key16.of(S.SipKey.of_octets(msg(16n)))

def key8.of(r: Result<&2, &2, S.SipError, H.HsipKey>) -> H.HsipKey:
  match r:
    case Done{k}:
      k
    case Fail{e}:
      H.HsipKey.of_words(0, 0)

def key8() -> H.HsipKey:
  key8.of(H.HsipKey.of_octets(msg(8n)))

def show_err(r: Result<&2, &2, S.SipError, B.Octets>) -> String:
  match r:
    case Done{o}:
      "accepted " ++ B.Octets.hex(o)
    case Fail{S.SipBadKeyLength{n}}:
      "refused " ++ Nat.show(n)

type ChkKind is Data:
  ChkSip64{}
  ChkSip128{}
  ChkHsip32{}
  ChkHsip64{}

def kind.name(k: ChkKind) -> String:
  match k:
    case ChkSip64{}:
      "sip64"
    case ChkSip128{}:
      "sip128"
    case ChkHsip32{}:
      "hsip32"
    case ChkHsip64{}:
      "hsip64"

def kind.run(k: ChkKind, +m: B.Octets) -> B.Octets:
  match k:
    case ChkSip64{}:
      S.siphash24(key16(), m)
    case ChkSip128{}:
      S.SipHash.hash(S.SipParams.sip24_wide(), key16(), m)
    case ChkHsip32{}:
      H.halfsiphash24(key8(), m)
    case ChkHsip64{}:
      H.HalfSipHash.hash(H.HalfSipParams.hsip24_wide(), key8(), m)

# the lines for messages of n - 1 down to 0 bytes, in front of acc
def table.go(+n: Nat, +k: ChkKind, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      table.go(p, k, kind.name(k) ++ " " ++ Nat.show(p) ++ " " ++ B.Octets.hex(kind.run(k, msg(p))) ++ "\\n" ++ acc)

def table(+k: ChkKind) -> String:
  table.go(64n, k, "")

# SipHash-2-4 of 63 bytes in three pieces (7, 1 and 55 bytes), and byte by
# byte through update_byte for the first 9
def pieces() -> B.Octets:
  +k = key16()
  S.SipHash.finish(S.SipHash.update(S.SipHash.update(S.SipHash.update(S.SipHash.start(S.SipParams.sip24(), k), B.Octets.take(7n, msg(63n))), B.Octets.slice(7n, 1n, msg(63n))), B.Octets.drop(8n, msg(63n))))

def bytes9.go(n: Nat, +i: U32, s: S.SipState) -> S.SipState:
  match n:
    case 0n:
      s
    case 1n+p:
      bytes9.go(p, U32.add(i, 1), S.SipHash.update_byte(s, i))

def bytes9() -> B.Octets:
  S.SipHash.finish(bytes9.go(9n, 0, S.SipHash.start(S.SipParams.sip24(), key16())))

def hpieces() -> B.Octets:
  +k = key8()
  H.HalfSipHash.finish(H.HalfSipHash.update(H.HalfSipHash.update(H.HalfSipHash.start(H.HalfSipParams.hsip24(), k), B.Octets.take(5n, msg(63n))), B.Octets.drop(5n, msg(63n))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(table(ChkSip64{}))
    IO.print(table(ChkSip128{}))
    IO.print(table(ChkHsip32{}))
    IO.print(table(ChkHsip64{}))
%(extra)s
'''


def main():
    check_openssl()
    lines, expect = [], []
    for name, arr in [("sip64", SIP64), ("sip128", SIP128), ("hsip32", HSIP32), ("hsip64", HSIP64)]:
        for i, h in enumerate(arr):
            expect.append("%s %d %s" % (name, i, h))
        expect.append("")  # each table ends with a newline before IO.print's own
    for label, expr, hexv in OPENSSL + MODEL:
        lines.append('    IO.print("%s " ++ B.Octets.hex(%s))' % (label, expr))
        expect.append("%s %s" % (label, hexv))
    lines.append('    IO.print("pieces " ++ B.Octets.hex(pieces()))')
    expect.append("pieces " + SIP64[63])
    lines.append('    IO.print("bytes9 " ++ B.Octets.hex(bytes9()))')
    expect.append("bytes9 " + SIP64[9])
    lines.append('    IO.print("hpieces " ++ B.Octets.hex(hpieces()))')
    expect.append("hpieces " + HSIP32[63])
    lines.append('    IO.print("key15 " ++ show_err(S.SipHash.mac(S.SipParams.sip24(), msg(15n), msg(3n))))')
    expect.append("key15 refused 15")
    lines.append('    IO.print("key16 " ++ show_err(S.SipHash.mac(S.SipParams.sip24(), msg(16n), msg(3n))))')
    expect.append("key16 accepted " + SIP64[3])
    lines.append('    IO.print("hkey16 " ++ show_err(H.HalfSipHash.mac(H.HalfSipParams.hsip24(), msg(16n), msg(3n))))')
    expect.append("hkey16 refused 16")
    lines.append('    IO.print("hkey8 " ++ show_err(H.HalfSipHash.mac(H.HalfSipParams.hsip24(), msg(8n), msg(3n))))')
    expect.append("hkey8 accepted " + HSIP32[3])
    text = HEAD % {"extra": "\n".join(lines)} + "\n" + "".join("#|%s\n" % e for e in expect)
    path = os.path.join(PKG, "check.bend")
    old = open(path).read() if os.path.exists(path) else ""
    if "--check" in sys.argv[1:]:
        if old != text:
            print("check.bend out of date (run gen/check.py)")
            sys.exit(1)
        print("check.bend up to date")
        return
    with open(path, "w", newline="\n") as f:
        f.write(text)


if __name__ == "__main__":
    main()
