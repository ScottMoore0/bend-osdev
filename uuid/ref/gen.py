#!/usr/bin/env python3
"""Differential test cases for bend-osdev-uuid.

Writes ref/cases.bend (a Bend program printing, for each UUID, what the
package reads and writes) and ref/expected.txt (the same from Python's uuid
module, which is outside this repository). Each case is a UUID from Python:
random version 4 ones, version 1, 3 and 5 ones, and random 128-bit values of
every variant. For each, the package must:
  * read its text form, in lower and in upper case, and write it back;
  * read its GUID-layout bytes (uuid.bytes_le) and give back its text, its
    bytes in RFC order (uuid.bytes), its GUID layout, its version field and
    its variant.
"""
import os, random, sys, uuid

VARIANTS = {
    uuid.RESERVED_NCS: "ncs",
    uuid.RFC_4122: "rfc9562",
    uuid.RESERVED_MICROSOFT: "microsoft",
    uuid.RESERVED_FUTURE: "future",
}

def bend_list(data):
    return "[" + ", ".join(str(b) for b in data) + "]"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    cases = [uuid.UUID(int=0), uuid.UUID(int=2 ** 128 - 1)]
    cases += [uuid.UUID(int=rng.getrandbits(128), version=4) for _ in range(40)]
    cases += [uuid.uuid1(node=rng.getrandbits(48), clock_seq=rng.getrandbits(14)) for _ in range(10)]
    cases += [uuid.uuid3(uuid.NAMESPACE_DNS, "host%d.example" % rng.getrandbits(32)) for _ in range(10)]
    cases += [uuid.uuid5(uuid.NAMESPACE_URL, "https://example.com/%d" % rng.getrandbits(32)) for _ in range(10)]
    # any version and variant: random bits, octet 8 forced into each range
    for top in (0x00, 0x80, 0xC0, 0xE0) * 10:
        b = bytearray(rng.getrandbits(8) for _ in range(16))
        b[8] = top | (b[8] & (0x7F if top == 0 else 0x3F if top == 0x80 else 0x1F))
        cases.append(uuid.UUID(bytes=bytes(b)))
    lines, expect = [], []
    for k, u in enumerate(cases):
        s = str(u)
        version = (u.int >> 76) & 15
        if u.variant == uuid.RFC_4122:
            assert version == u.version
        lines.append('    IO.print("%d " ++ row(U.Uuid.parse("%s"), U.Uuid.parse("%s"), U.Uuid.from_guid(B.Octets.of_list(%s))))' % (k, s, s.upper(), bend_list(u.bytes_le)))
        expect.append("%d %s %s %s %s %s v%d %s" % (k, s, s, s, u.bytes.hex(), u.bytes_le.hex(), version, VARIANTS[u.variant]))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("""import Base
import ../../bytes/bytes.bend as B
import ../uuid.bend as U

def show_m(m: Result<&2, &2, U.UuidError, U.Uuid>) -> String:
  match m:
    case Done{u}:
      U.Uuid.show(u)
    case Fail{e}:
      U.UuidError.show(e)

def info(m: Result<&2, &2, U.UuidError, U.Uuid>) -> String:
  match m:
    case Done{+u}:
      U.Uuid.show(u) ++ " " ++ B.Octets.hex(U.Uuid.to_bytes(u)) ++ " " ++ B.Octets.hex(U.Uuid.to_guid(u)) ++ " v" ++ U32.show(U.Uuid.version(u)) ++ " " ++ U.UuidVariant.show(U.Uuid.variant(u))
    case Fail{e}:
      U.UuidError.show(e)

def row(a: Result<&2, &2, U.UuidError, U.Uuid>, b: Result<&2, &2, U.UuidError, U.Uuid>, g: Result<&2, &2, U.UuidError, U.Uuid>) -> String:
  show_m(a) ++ " " ++ show_m(b) ++ " " ++ info(g)

def main() -> IO(Unit):
  do IO<Unit>:
""")
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
