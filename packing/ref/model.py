"""A model of bend-osdev-packing's layout, written from the quirks' documented
meaning as index arithmetic (where bit k of the buffer is), independently of
the package's list transformations."""

def position(L, k, msb_right, little_endian, lsw32_first):
    """The byte index and the bit mask in the buffer of bit k."""
    lb = k // 8                 # logical byte, counted from the least significant
    bb = k % 8                  # bit within it
    m = L - 1 - lb              # logical byte, counted from the most significant
    wi, bi = m // 4, m % 4      # its 4-byte word and its place in the word
    nw = L // 4
    if lsw32_first:
        wi = nw - 1 - wi
    if little_endian:
        bi = 3 - bi
    phys = wi * 4 + bi if (lsw32_first or little_endian) else m
    bit = (7 - bb) if msb_right else bb
    return phys, 1 << bit

def check(L, start, end, quirks):
    if start < end:
        return "PkBadRange"
    if start - end + 1 > 64:
        return "PkTooWide"
    if start >= 8 * L:
        return "PkOutOfBuffer"
    if (quirks[1] or quirks[2]) and L % 4 != 0:
        return "PkBadLength"
    return None

def unpack(buf, start, end, quirks):
    e = check(len(buf), start, end, quirks)
    if e:
        return e
    v = 0
    for i, k in enumerate(range(end, start + 1)):
        p, msk = position(len(buf), k, *quirks)
        if buf[p] & msk:
            v |= 1 << i
    return "%016x" % v

def pack(buf, start, end, v, quirks, masked=False):
    e = check(len(buf), start, end, quirks)
    if e:
        return e
    w = start - end + 1
    if not masked and v >> w:
        return "PkOverflow"
    out = list(buf)
    for i, k in enumerate(range(end, start + 1)):
        p, msk = position(len(buf), k, *quirks)
        if (v >> i) & 1:
            out[p] |= msk
        else:
            out[p] &= ~msk & 255
    return "".join("%02x" % b for b in out)

def bit(buf, k, quirks):
    if k >= 8 * len(buf):
        return False
    p, msk = position(len(buf), k, *quirks)
    return bool(buf[p] & msk)
