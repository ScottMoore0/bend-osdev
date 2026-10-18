#!/usr/bin/env python3
"""Differential test cases for bend-osdev-crc.

Writes ref/cases.bend (a Bend program printing each CRC of each case) and
ref/expected.txt (the same values from implementations outside this
repository):
  * CRC-32: Python's binascii.crc32 (zlib);
  * CRC-64/XZ: the check field of a real .xz stream (Python's lzma);
  * CRC32C: the superblock checksum mke2fs writes with metadata_csum
    (ext4 stores the raw register: seed ~0, no final XOR), when mke2fs is
    installed;
  * all of them: an independent bitwise implementation of the Rocksoft
    parameter model, written here from the model's definition.
"""
import binascii, lzma, os, random, shutil, struct, subprocess, sys, tempfile

def reflect(x, w):
    return int(format(x, "0%db" % w)[::-1], 2)

def model(data, w, poly, init, refl, xorout):
    mask = (1 << w) - 1
    if refl:
        c, p = reflect(init, w), reflect(poly, w)
        for b in data:
            c ^= b
            for _ in range(8):
                c = (c >> 1) ^ p if c & 1 else c >> 1
        return (c ^ xorout) & mask
    c = init
    if w < 8:
        # a byte does not fit at the top: its bits enter one at a time
        for b in data:
            for i in range(7, -1, -1):
                top = (c >> (w - 1) & 1) ^ (b >> i & 1)
                c = ((c << 1) ^ poly) & mask if top else (c << 1) & mask
        return (c ^ xorout) & mask
    for b in data:
        c ^= b << (w - 8)
        for _ in range(8):
            c = ((c << 1) ^ poly) & mask if c >> (w - 1) & 1 else (c << 1) & mask
    return (c ^ xorout) & mask

ONES = 2 ** 64 - 1
CRCS = [  # name, width, poly, init, reflected, xorout
    ("crc32c", 32, 0x1EDC6F41, 0xFFFFFFFF, True, 0xFFFFFFFF),
    ("crc32", 32, 0x04C11DB7, 0xFFFFFFFF, True, 0xFFFFFFFF),
    ("crc16", 16, 0x8005, 0, True, 0),
    ("crc_t10dif", 16, 0x8BB7, 0, False, 0),
    ("crc64_ecma", 64, 0x42F0E1EBA9EA3693, 0, False, 0),
    ("crc64_xz", 64, 0x42F0E1EBA9EA3693, ONES, True, ONES),
    ("crc64_nvme", 64, 0xAD93D23594C93659, ONES, True, ONES),
    ("crc4_itu", 4, 0x3, 0, True, 0),
    ("crc7_mmc", 7, 0x09, 0, False, 0),
    ("crc8_smbus", 8, 0x07, 0, False, 0),
    ("crc8_itu", 8, 0x07, 0, False, 0x55),
    ("crc8_maxim", 8, 0x31, 0, True, 0),
    ("crc8_dvb_s2", 8, 0xD5, 0, False, 0),
    ("crc8_autosar", 8, 0x2F, 0xFF, False, 0xFF),
    ("crc16_kermit", 16, 0x1021, 0, True, 0),
    ("crc16_ccitt_false", 16, 0x1021, 0xFFFF, False, 0),
    ("crc16_xmodem", 16, 0x1021, 0, False, 0),
]
# the catalogue's check values of "123456789", against which the model is
# checked before it is used
CHECKS = {"crc32c": 0xE3069283, "crc32": 0xCBF43926, "crc16": 0xBB3D, "crc_t10dif": 0xD0DB, "crc4_itu": 0x7,
          "crc7_mmc": 0x75, "crc8_smbus": 0xF4, "crc8_itu": 0xA1, "crc8_maxim": 0xA1, "crc8_dvb_s2": 0xBC,
          "crc8_autosar": 0xDF, "crc16_kermit": 0x2189, "crc16_ccitt_false": 0x29B1, "crc16_xmodem": 0x31C3}

def xz_crc64(data):
    # an .xz stream ends: block check (8 bytes for CRC64), index, footer (12)
    raw = lzma.compress(data, format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64)
    # the index is 4-byte aligned; its size is in the footer, as (n + 1) * 4
    backward = (struct.unpack("<I", raw[-8:-4])[0] + 1) * 4
    check = raw[-12 - backward - 8:-12 - backward]
    return struct.unpack("<Q", check)[0]

def ext4_crc32c_cases():
    """(superblock bytes 0..1019, stored checksum) from a fresh mke2fs image."""
    if not shutil.which("mke2fs"):
        return []
    out = []
    with tempfile.TemporaryDirectory() as d:
        for i in range(3):
            img = os.path.join(d, "fs%d.img" % i)
            with open(img, "wb") as f:
                f.truncate(4 * 1024 * 1024)
            subprocess.run(["mke2fs", "-q", "-F", "-t", "ext4", "-O", "metadata_csum", "-U", "random", img], check=True)
            with open(img, "rb") as f:
                f.seek(1024)
                sb = f.read(1024)
            out.append((sb[:1020], struct.unpack("<I", sb[1020:1024])[0]))
    return out

def bend_list(data):
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    short = [b"", b"a", b"123456789"] + [bytes(rng.randrange(256) for _ in range(rng.randrange(1, 64))) for _ in range(12)]
    long = [bytes(rng.randrange(256) for _ in range(rng.randrange(64, 400))) for _ in range(8)]
    for name, w, poly, init, refl, xo in CRCS:
        if name in CHECKS:
            assert model(b"123456789", w, poly, init, refl, xo) == CHECKS[name], name
    lines, expect = [], []
    for k, data in enumerate(short + long):
        for name, w, poly, init, refl, xo in CRCS:
            if w == 64 and len(data) > 100:
                continue  # W64 is slow; the long cases cover the 32-bit CRCs
            v = model(data, w, poly, init, refl, xo)
            if name == "crc32":
                assert v == binascii.crc32(data), "model disagrees with zlib"
            if name == "crc64_xz" and data:  # an empty .xz stream has no block, so no check
                assert v == xz_crc64(data), "model disagrees with xz"
            show = "W.W64.show_hex" if w == 64 else "U32.show"
            lines.append('    IO.print("%s %d " ++ %s(C.%s(%s)))' % (name, k, show, name, bend_list(data)))
            expect.append("%s %d %s" % (name, k, ("%016x" % v) if w == 64 else str(v)))
            # the table-driven fast path, on the same input
            fast = "T.Crc64Spec.compute_fast" if w == 64 else "T.Crc32Spec.compute_fast"
            lines.append('    IO.print("%s_fast %d " ++ %s(%s(C.%s.spec(), %s)))' % (name, k, show, fast, name, bend_list(data)))
            expect.append("%s_fast %d %s" % (name, k, ("%016x" % v) if w == 64 else str(v)))
    for k, (sb, stored) in enumerate(ext4_crc32c_cases()):
        assert model(sb, 32, 0x1EDC6F41, 0xFFFFFFFF, True, 0) == stored, "model disagrees with mke2fs"
        lines.append('    IO.print("ext4_sb %d " ++ U32.show(C.Crc32Spec.update(C.crc32c.spec(), 4294967295, %s)))' % (k, bend_list(sb)))
        expect.append("ext4_sb %d %d" % (k, stored))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../word64/word64.bend as W\nimport ../../bytes/bytes.bend as B\nimport ../crc.bend as C\nimport ../table.bend as T\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
