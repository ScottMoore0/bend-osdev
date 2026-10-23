"""A model of bend-osdev-jitter with the XDRBG conditioner, written from
the documents the package cites, not from its Bend code: Müller's "CPU Time
Jitter Based Non-Physical True Random Number Generator" (4 May 2026),
section 3.1.1 (the XDRBG seeding, reseeding and generate operations, the
seed as the concatenation of the insertion buffers, |V| = 512 bits, an
output of 256 bits, alpha a NULL buffer) and section 3.1.7 (the 1,088-bit
buffer), and Kelsey, Lucks and Müller's "XDRBG" (IACR ToSC 2024(1)),
Algorithm 2 and appendix B (the encode function); SHAKE256 and SHA3-256
from Python's hashlib.

Everything else (the stuck test, the health tests, the buffer of each
delta, which blocks are discarded) is model.py's. Unlike the package, which
feeds each buffer to SHAKE256 as it arrives, this model keeps the whole
seed and hashes it in one call when a block is taken.
"""
import hashlib

import model

VSIZE = 64   # |V|, 512 bits (XDRBG-256)
OUTSIZE = 32  # l, 256 bits


def encode(s, alpha, n):
    """ToSC appendix B: S || alpha || (n * 85 + |alpha|/8) as one byte"""
    assert len(alpha) <= 84 and n in (0, 1, 2)
    return s + alpha + bytes([n * 85 + len(alpha)])


def xof(x, nbytes):
    return hashlib.shake_256(x).digest(nbytes)


class Seed:
    """the pool: the seed collected so far"""

    def __init__(self):
        self.data = b""

    def update(self, b):
        self.data += b


class Jitter(model.Jitter):
    def __init__(self, p, alpha=b"", vsize=VSIZE, outsize=OUTSIZE):
        super().__init__(p)
        self.alpha, self.vsize, self.outsize = alpha, vsize, outsize
        self.v = None  # no XDRBG state before the first block
        self.pool = Seed()

    def take(self):
        seed = self.pool.data
        if self.v is None:  # Algorithm 2, INSTANTIATE
            v = xof(encode(seed, self.alpha, 0), self.vsize)
        else:  # RESEED, from the state the last GENERATE left
            v = xof(encode(self.v + seed, self.alpha, 1), self.vsize)
        t = xof(encode(v, self.alpha, 2), self.outsize + self.vsize)  # GENERATE
        self.v, out = t[:self.vsize], t[self.vsize:]
        self.pool = Seed()
        self.count = 0
        return out
