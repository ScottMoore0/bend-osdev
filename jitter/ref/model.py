"""A model of bend-osdev-jitter, written from the documents the package
cites, not from its Bend code: Müller's "CPU Time Jitter Based
Non-Physical True Random Number Generator" (4 May 2026), sections 3.1.4 to
3.1.7 and 3.2, for the stuck test, the insertion of each delta and the
blocks, and NIST SP 800-90B (January 2018), sections 4.4.1 and 4.4.2, for
the Repetition Count and Adaptive Proportion Tests; SHA3-256 from Python's
hashlib. The conditioner layout is the package's (README.md, "The
conditioning"): delta, domain separator, digest of the health tests'
status, zeros to the 136-byte SHA3-256 rate.
"""
import hashlib

M64 = (1 << 64) - 1
RATE = 136

APT_CUTOFF = {1: 325, 2: 422, 3: 459, 4: 477, 5: 488, 6: 494, 7: 499, 8: 502, 9: 505,
              10: 507, 11: 508, 12: 509, 13: 510, 14: 511}


def params(osr=3):
    return dict(osr=osr, safety=65, rct_cutoff=1 + 30 * osr, apt_window=512,
                apt_cutoff=APT_CUTOFF.get(osr, 512), domain=2, prime=1)


class Stuck:
    def __init__(self):
        self.prev, self.prev2 = 0, 0

    def step(self, t):
        t2 = (t - self.prev) & M64
        t3 = (t2 - self.prev2) & M64
        stuck = t == 0 or t2 == 0 or t3 == 0
        self.prev, self.prev2 = t, t2
        return stuck


class Rct:  # SP 800-90B 4.4.1
    def __init__(self, c):
        self.c, self.a, self.b, self.started, self.failed = c, 0, 0, False, False

    def feed(self, x):
        if not self.started:
            self.a, self.b, self.started = x, 1, True
        elif x == self.a:
            self.b += 1
            if self.b >= self.c:
                self.failed = True
        else:
            self.a, self.b = x, 1


class Apt:  # SP 800-90B 4.4.2
    def __init__(self, w, c):
        self.w, self.c, self.a, self.b, self.i, self.open, self.failed = w, c, 0, 0, 0, False, False

    def feed(self, x):
        if not self.open:
            self.a, self.b, self.i = x, 1, 1
        else:
            self.i += 1
            if x == self.a:
                self.b += 1
                if self.b >= self.c:
                    self.failed = True
        self.open = self.i < self.w


class Jitter:
    def __init__(self, p):
        self.p = p
        self.pool = hashlib.sha3_256()
        self.stuck = Stuck()
        self.rct = Rct(p["rct_cutoff"])
        self.apt = Apt(p["apt_window"], p["apt_cutoff"])
        self.count = 0
        self.discard = p["prime"]

    def need(self):
        return (256 + self.p["safety"]) * self.p["osr"]

    def failed(self):
        return self.rct.failed or self.apt.failed

    def absorb(self, d):
        self.rct.feed(d)
        self.apt.feed(d)
        aux = b"".join(v.to_bytes(4, "little") for v in
                       (self.rct.b, self.apt.b, self.p["apt_cutoff"], self.p["apt_window"]))
        aux += self.apt.a.to_bytes(8, "little")
        dig = hashlib.sha3_256(aux).digest()
        buf = d.to_bytes(8, "little") + bytes([self.p["domain"] & 255]) + dig
        buf += bytes(max(0, RATE - len(buf)))
        self.pool.update(buf)
        if not self.stuck.step(d):
            self.count += 1

    def can_block(self):
        return not self.failed() and self.count >= self.need()

    def take(self):
        out = self.pool.digest()
        self.pool = hashlib.sha3_256(out)
        self.count = 0
        return out

    def why(self):
        if self.rct.failed:
            return "rct"
        if self.apt.failed:
            return "apt"
        return "not enough"

    def read(self, ds, n):
        """n bytes from the deltas: ('ok', bytes, deltas used) or (error,
        bytes collected, deltas used)"""
        acc = b""
        used = 0
        if n <= 0:
            return "ok", b"", 0
        if self.failed():
            return self.why(), b"", 0
        for d in ds:
            used += 1
            self.absorb(d)
            if self.can_block():
                out = self.take()
                if self.discard > 0:
                    self.discard -= 1
                else:
                    acc += out
            if len(acc) >= n:
                return "ok", acc[:n], used
            if self.failed():
                return self.why(), acc, used
        return "need more", acc, used
