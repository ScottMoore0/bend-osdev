#!/usr/bin/env python3
"""Differential test cases for bend-osdev-ccm: its slice of the test the
modes had together in bend-osdev-cipher-modes (the random cases of the other
modes are drawn too, so that every slice sees the same keys and messages,
but only this package's are written).

Writes ref/cases.bend (a Bend program printing each mode's output on each
case) and ref/expected.txt (the same outputs from Python's cryptography
package, an implementation outside this repository): AES block encryption and
decryption, CBC with and without PKCS #7 padding, XTS (with ciphertext
stealing), CCM (encryption, decryption, and a tampered tag), and CMAC (one
call, and in two pieces), on random keys, IVs, tweaks, nonces and messages.
"""
import os, random, sys
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESCCM
from cryptography.hazmat.primitives import cmac, padding

def run(mode, key, data, enc=True):
    c = Cipher(algorithms.AES(key), mode)
    op = c.encryptor() if enc else c.decryptor()
    return op.update(data) + op.finalize()

def o(data):
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    rb = lambda n: bytes(rng.randrange(256) for _ in range(n))
    lines, expect = [], []
    def case(name, k, call, want):
        if not name.startswith('ccm'):
            return
        lines.append('    IO.print("%s %d " ++ %s)' % (name, k, call))
        expect.append("%s %d %s" % (name, k, want))

    for k in range(8):  # one block, AES-128 and AES-256
        key, p = rb(16 if k % 2 == 0 else 32), rb(16)
        c = run(modes.ECB(), key, p)
        case("aes_enc", k, "blk(X.CmAes.key(%s), %s, True{})" % (o(key), o(p)), c.hex())
        case("aes_dec", k, "blk(X.CmAes.key(%s), %s, False{})" % (o(key), o(c)), p.hex())

    for k in range(16):  # CBC, whole blocks (two of 1 KiB)
        key, iv, p = rb(16 if k % 2 == 0 else 32), rb(16), rb(16 * (64 if k >= 14 else rng.randrange(0, 6)))
        c = run(modes.CBC(iv), key, p)
        case("cbc_enc", k, "res(D.CmAes.cbc_encrypt(%s, %s, %s))" % (o(key), o(iv), o(p)), c.hex())
        case("cbc_dec", k, "res(D.CmAes.cbc_decrypt(%s, %s, %s))" % (o(key), o(iv), o(c)), p.hex())

    for k in range(16):  # CBC with PKCS #7 padding, any length
        key, iv, p = rb(16 if k % 2 == 0 else 32), rb(16), rb(rng.randrange(0, 70) if k < 15 else 1000)
        pad = padding.PKCS7(128).padder()
        c = run(modes.CBC(iv), key, pad.update(p) + pad.finalize())
        case("cbcp_enc", k, "res(D.CmAes.cbc_encrypt_padded(%s, %s, %s))" % (o(key), o(iv), o(p)), c.hex())
        case("cbcp_dec", k, "res(D.CmAes.cbc_decrypt_padded(%s, %s, %s))" % (o(key), o(iv), o(c)), p.hex())

    for k in range(36):  # XTS: every tail length 0 to 15 after one block and after several, and 512-byte sectors
        key, tw = rb(32 if k % 2 == 0 else 64), rb(16)
        n = 16 + k if k < 16 else 16 * rng.randrange(2, 8) + (k - 16) if k < 32 else 512 + (0 if k < 34 else rng.randrange(1, 16))
        p = rb(n)
        c = run(modes.XTS(tw), key, p)
        case("xts_enc", k, "res(D.CmAes.xts_encrypt(%s, %s, %s))" % (o(key), o(tw), o(p)), c.hex())
        case("xts_dec", k, "res(D.CmAes.xts_decrypt(%s, %s, %s))" % (o(key), o(tw), o(c)), p.hex())

    for k in range(20):  # CCM: every tag length and nonce length among them, and a 1000-byte message
        key = rb(16 if k % 2 == 0 else 32)
        m = [4, 6, 8, 10, 12, 14, 16][k % 7]
        nonce, aad, p = rb(7 + k % 7), rb(rng.choice([0, 0, rng.randrange(1, 40)])), rb(rng.randrange(0, 60) if k < 19 else 1000)
        c = AESCCM(key, tag_length=m).encrypt(nonce, p, aad)
        bad = c[:-1] + bytes([c[-1] ^ 1])
        case("ccm_enc", k, "res(D.CmAes.ccm_encrypt(%s, %dn, %s, %s, %s))" % (o(key), m, o(nonce), o(aad), o(p)), c.hex())
        case("ccm_dec", k, "res(D.CmAes.ccm_decrypt(%s, %dn, %s, %s, %s))" % (o(key), m, o(nonce), o(aad), o(c)), p.hex())
        case("ccm_bad", k, "res(D.CmAes.ccm_decrypt(%s, %dn, %s, %s, %s))" % (o(key), m, o(nonce), o(aad), o(bad)), "fail CmTagMismatch")

    for k in range(20):  # CMAC, in one call and in two pieces
        key, p = rb(16 if k % 2 == 0 else 32), rb(rng.choice([0, 16, 32, rng.randrange(1, 80)]) if k < 19 else 1500)
        mac = cmac.CMAC(algorithms.AES(key))
        mac.update(p)
        t = mac.finalize()
        cut = rng.randrange(0, len(p) + 1)
        case("cmac", k, "res(D.CmAes.cmac(%s, %s))" % (o(key), o(p)), t.hex())
        case("cmac2", k, "cmac2(X.CmAes.key(%s), %s, %s)" % (o(key), o(p[:cut]), o(p[cut:])), t.hex())

    for k in range(6):  # one block, AES-192 (CmAes.key192)
        key, p = rb(24), rb(16)
        c = run(modes.ECB(), key, p)
        case("aes192_enc", k, "blk(X.CmAes.key192(%s), %s, True{})" % (o(key), o(p)), c.hex())
        case("aes192_dec", k, "blk(X.CmAes.key192(%s), %s, False{})" % (o(key), o(c)), p.hex())

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("""import Base
import ../../bytes/bytes.bend as B
import ../../mode-core/mode-core.bend as M
import ../../aes/aes.bend as X
import ../../cmac/cmac.bend as CM
import ../../aes-modes/aes-modes.bend as D

def err(e: M.CmError) -> String:
  match e:
    case M.CmBadKeyLength{n}:
      "CmBadKeyLength"
    case M.CmBadIvLength{n}:
      "CmBadIvLength"
    case M.CmBadTweakLength{n}:
      "CmBadTweakLength"
    case M.CmBadNonceLength{n}:
      "CmBadNonceLength"
    case M.CmBadTagLength{n}:
      "CmBadTagLength"
    case M.CmBadBlockSize{n}:
      "CmBadBlockSize"
    case M.CmNotBlockMultiple{n}:
      "CmNotBlockMultiple"
    case M.CmTooShort{n}:
      "CmTooShort"
    case M.CmTooLong{n}:
      "CmTooLong"
    case M.CmBadPadding{}:
      "CmBadPadding"
    case M.CmTagMismatch{}:
      "CmTagMismatch"

def res(r: Result<&2, &2, M.CmError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail " ++ err(e)
    case Done{v}:
      B.Octets.hex(v)

def blk.go(enc: Bool, +k: X.CmAesKey, b: M.CmBlock) -> String:
  match enc:
    case True{}:
      M.CmBlock.hex(X.CmAes.encrypt(k, b))
    case False{}:
      M.CmBlock.hex(X.CmAes.decrypt(k, b))

def blk.of(m: Maybe<&2, M.CmBlock>) -> M.CmBlock:
  match m:
    case None{}:
      M.CmBlock.zero()
    case Some{b}:
      b

def blk(r: Result<&2, &2, M.CmError, X.CmAesKey>, o: B.Octets, enc: Bool) -> String:
  match r:
    case Fail{e}:
      "fail " ++ err(e)
    case Done{k}:
      blk.go(enc, k, blk.of(M.CmBlock.of_octets(o)))

def cmac2(r: Result<&2, &2, M.CmError, X.CmAesKey>, a: B.Octets, b: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail " ++ err(e)
    case Done{+k}:
      B.Octets.hex(CM.Cmac.finish(~X.CmAesKey, ~X.CmAes.encrypt, k, CM.Cmac.update(~X.CmAesKey, ~X.CmAes.encrypt, k, CM.Cmac.update(~X.CmAesKey, ~X.CmAes.encrypt, k, CM.Cmac.start(), a), b)))

def main() -> IO(Unit):
  do IO<Unit>:
""" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
