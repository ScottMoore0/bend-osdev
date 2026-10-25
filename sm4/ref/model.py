"""An independent Python model of the sm4 package's cipher (SM4).

Written here from the specification (not from any implementation), by the
same author as the Bend package, so agreement with it is weaker evidence
than agreement with an outside library. ref/gen.py compares the package
with this model, and also with Python's cryptography, and checks
the model against the specification's published vectors first.
"""

M32 = 0xFFFFFFFF


def rol(x, n):
    n %= 32
    return ((x << n) | (x >> (32 - n))) & M32 if n else x


def ror(x, n):
    return rol(x, 32 - n % 32)


def words_le(b):
    return [int.from_bytes(b[4 * i:4 * i + 4], "little") for i in range(len(b) // 4)]


def bytes_le(ws):
    return b"".join(w.to_bytes(4, "little") for w in ws)


# ---------------------------------------------------------------- SM4
# GB/T 32907-2016 (English description: draft-ribose-cfrg-sm4, RFC 8998).

SM4_S = bytes.fromhex(
    "d690e9fecce13db716b614c228fb2c05" "2b679a762abe04c3aa44132649860699"
    "9c4250f491ef987a33540b43edcfac62" "e4b31ca9c908e89580df94fa758f3fa6"
    "4707a7fcf37317ba83593c19e6854fa8" "686b81b27164da8bf8eb0f4b70569d35"
    "1e240e5e6358d1a225227c3b01217887" "d40046579fd327524c3602e7a0c4c89e"
    "eabf8ad240c738b5a3f7f2cef96115a1" "e0ae5da49b341a55ad933230f58cb1e3"
    "1df6e22e8266ca60c02923ab0d534e6f" "d5db3745defd8e2f03ff6a726d6c5b51"
    "8d1baf92bbddbc7f11d95c411f105ad8" "0ac13188a5cd7bbd2d74d012b8e5b4b0"
    "8969974a0c96777e65b9f109c56ec684" "18f07dec3adc4d2079ee5f3ed7cb3948")
SM4_FK = [0xA3B1BAC6, 0x56AA3350, 0x677D9197, 0xB27022DC]


def sm4_tau(x):
    return int.from_bytes(bytes(SM4_S[b] for b in x.to_bytes(4, "big")), "big")


def sm4_t(x):
    b = sm4_tau(x)
    return b ^ rol(b, 2) ^ rol(b, 10) ^ rol(b, 18) ^ rol(b, 24)


def sm4_t_key(x):
    b = sm4_tau(x)
    return b ^ rol(b, 13) ^ rol(b, 23)


def sm4_keys(key):
    k = [int.from_bytes(key[4 * i:4 * i + 4], "big") ^ SM4_FK[i] for i in range(4)]
    rk = []
    for i in range(32):
        ck = int.from_bytes(bytes(((4 * i + j) * 7) & 255 for j in range(4)), "big")
        k.append(k[i] ^ sm4_t_key(k[i + 1] ^ k[i + 2] ^ k[i + 3] ^ ck))
        rk.append(k[-1])
    return rk


def sm4_block(block, rk):
    x = [int.from_bytes(block[4 * i:4 * i + 4], "big") for i in range(4)]
    for i in range(32):
        x.append(x[i] ^ sm4_t(x[i + 1] ^ x[i + 2] ^ x[i + 3] ^ rk[i]))
    return b"".join(w.to_bytes(4, "big") for w in x[:-5:-1])


def sm4_encrypt(key, block):
    return sm4_block(block, sm4_keys(key))


def sm4_decrypt(key, block):
    return sm4_block(block, sm4_keys(key)[::-1])
