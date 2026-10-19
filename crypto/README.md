# bend-osdev-crypto

One set of typed interfaces for every cryptographic algorithm in bend-osdev,
the Bend counterpart of Linux's crypto API: block cipher, stream cipher,
hash, MAC, AEAD, KDF, signature and key agreement, each with its laws; the
generic algorithms built on them (HMAC and HKDF over any hash; PBKDF2 and
the SP 800-108 KDFs in counter and feedback mode over any MAC; ECB, CBC, CTR, PCBC and CBC-CS3 ciphertext stealing over any block
cipher of any block size; LRW over any 128-bit one; the MACs XCBC and VMAC
over any block cipher); and the existing algorithms (cipher-modes' AES,
CMAC and CCM; legacy-ciphers' DES, 3DES, SM4, Camellia, Serpent, Twofish,
ARIA, CAST-256, Blowfish, CAST-128, TEA, XTEA, FCrypt and RC4; crc's CRCs;
the hashes package's MD4, MD5, SHA-1, RIPEMD-160, SM3, Streebog-256 and
Streebog-512, and its Michael as a MAC) and bend-collections' SHA-256,
SHA-512 and SHA3-256 as instances, with their interface laws proved or
tested; and HMAC-SHA-256, HMAC-SHA-512, HMAC-SHA3-256, HKDF-SHA-256,
PBKDF2-HMAC-SHA-256, PBKDF2-HMAC-SHA-1 and KBKDF-HMAC-SHA-256 (counter and
feedback mode) over those. The public-key algorithms (RSA, DH, ECDSA, ECDH,
SM2, EC-RDSA) are instances of the signature and key-agreement interfaces
in bend-osdev-pubkey, which keeps their big-integer dependencies out of this
package.

The directory is `crypto` and the entry file `crypto/crypto.bend`; the hub
name is `bend-osdev-crypto`.

## Specifications

Written from the public specifications only:

* **ECB, CBC, CTR:** NIST SP 800-38A, *Recommendation for Block Cipher Modes
  of Operation* (2001), sections 6.1, 6.2 and 6.5, and Appendix B.1 (the
  standard incrementing function); vectors from Appendix F.1, F.2 and F.5.
* **PCBC:** the FCrypt specification's "Modes of operation" (T. Anderson,
  openafs-devel, December 2000), as Kerberos version 4 uses it; vector from
  the same text.
* **LRW:** M. Liskov, R. Rivest, D. Wagner, *Tweakable Block Ciphers*
  (CRYPTO 2002), theorem 2, as the IEEE P1619 draft proposal *Tweakable
  Narrow-block Encryption* (draft 1.00, October 2004) specifies LRW-AES;
  vectors from its Annex B.
* **CBC-CS3:** NIST SP 800-38A Addendum, *Three Variants of Ciphertext
  Stealing for CBC Mode* (2010); vectors from RFC 3962, *Advanced
  Encryption Standard (AES) Encryption for Kerberos 5* (2005), Appendix B
  (Kerberos's CTS is CS3).
* **XCBC-MAC:** RFC 3566, *The AES-XCBC-MAC-96 Algorithm and Its Use With
  IPsec* (2003), and its test cases 1 to 7.
* **VMAC:** T. Krovetz, W. Dai, *VMAC: Message Authentication Code using
  Universal Hashing* (draft-krovetz-vmac-01, 2007); vectors from its
  appendix (VMAC-64 and VMAC-128 over AES-128).
* **HMAC:** RFC 2104, *HMAC: Keyed-Hashing for Message Authentication*
  (1997), and FIPS 198-1, *The Keyed-Hash Message Authentication Code*
  (2008).
* **HKDF:** RFC 5869, *HMAC-based Extract-and-Expand Key Derivation
  Function* (2010).
* **SHA-256, SHA-512:** FIPS 180-4, *Secure Hash Standard* (2015), as
  bend-collections implements it; vectors from FIPS 180-4's examples, RFC
  4231, *Identifiers and Test Vectors for HMAC-SHA-224, HMAC-SHA-256,
  HMAC-SHA-384, and HMAC-SHA-512* (2005), test cases 1 to 7, and RFC 5869's
  Appendix A.1 to A.3.
* **SHA3-256:** FIPS 202, *SHA-3 Standard: Permutation-Based Hash and
  Extendable-Output Functions* (2015), as bend-collections implements it;
  vectors from NIST's SHA-3 examples (the empty message, "abc", 200 bytes
  of a3).
* **PBKDF2:** RFC 8018, K. Moriarty, B. Kaliski and A. Rusch, *PKCS #5:
  Password-Based Cryptography Specification Version 2.1* (2017), section
  5.2; vectors from RFC 6070, S. Josefsson, *PKCS #5: Password-Based Key
  Derivation Function 2 (PBKDF2) Test Vectors* (2011), test cases 1 to 3,
  5 and 6 (PBKDF2-HMAC-SHA1), and RFC 7914, C. Percival and S. Josefsson,
  *The scrypt Password-Based Key Derivation Function* (2016), section 11
  (PBKDF2-HMAC-SHA256).
* **SP 800-108 KDFs:** NIST SP 800-108r1-upd1 (L. Chen, *Recommendation
  for Key Derivation Using Pseudorandom Functions*, August 2022, with
  updates as of February 2, 2024): section 4 (the fixed input data Label || 0x00 || Context
  || [L]_2), 4.1 (counter mode), 4.2 (feedback mode, with and without the
  counter). No published test vectors were used (NIST's CAVP files are a
  download, which this work does not do); Python's cryptography's
  KBKDFHMAC stands in for counter mode.
* **HMAC-MD5, HMAC-SHA-1:** RFC 2202, P. Cheng and R. Glenn, *Test Cases
  for HMAC-MD5 and HMAC-SHA-1* (1997), test cases 1 and 2.
* **The hashes package's hashes and Michael:** the specifications
  hashes/README.md cites (RFC 1320, RFC 1321, FIPS 180-4, the RIPEMD-160
  paper, GB/T 32905, RFC 6986, IEEE 802.11i). Michael's algorithm is
  checked against Wool (IEEE Trans. Wireless Commun. 3(5), 2004, Fig. 1)
  and Huang, Seberry, Susilo and Bunder (LNCS 3823, 2005, section 2), and
  with its byte order end to end against IEEE 802.11-2012 M.6.3's TKIP
  test vector (as hostap's BSD-licensed `wlantest/test_vectors.c` gives
  its data); its six chained test vectors are not checked against a
  published copy of the standard, which could not be read
  (hashes/README.md).
* **AEAD:** the shape of RFC 5116, *An Interface and Algorithms for
  Authenticated Encryption* (2008).
* The instances follow their own packages' specifications (FIPS 197, FIPS
  46-3, SP 800-67, GB/T 32907-2016, RFC 3713, the Serpent and Twofish
  papers, RFC 5794 (ARIA), RFC 2612 (CAST-256), Schneier's Blowfish paper,
  RFC 2144 (CAST-128), the TEA and XTEA papers, the FCrypt specification,
  RFC 6229, SP 800-38B and RFC 4493, SP 800-38C and RFC 3610, the
  Rocksoft CRC model); `check.bend` runs those specifications' vectors
  through the interfaces.

## Files

| File | Holds |
|---|---|
| `crypto.bend` | the error type `CrError` every interface reports, and its helpers |
| `block.bend` | the block-cipher interface, and one block of bytes through it |
| `stream.bend` | the stream-cipher interface; keystream generators (`CrKsStep`) and `CrXor`, which makes any of them a stream cipher |
| `hash.bend` | the hash interface, and a digest of pieces |
| `mac.bend` | the MAC interface, and its named default verify (`CrMac.verify_tag`) |
| `aead.bend` | the AEAD interface, and seal and open under a raw key |
| `kdf.bend` | the KDF interface, and a key for any interface derived from a secret |
| `sign.bend` | the signature interface, key pairs, and verification from a public key's bytes |
| `kex.bend` | the key-agreement interface, and agreement from key bytes |
| `modes.bend` | ECB and CBC (on blocks and on bytes) and CTR (a keystream generator) over any block cipher |
| `octets.bend` | byte-string helpers the newer modes share: XOR over the first operand's length, a byte repeated, a message cut into pieces of a block size |
| `pcbc.bend` | PCBC over any block cipher (on blocks and on bytes) |
| `lrw.bend` | LRW over any 128-bit block cipher (on blocks and on bytes), its tweaks through bend-osdev-gf's GF(2^128) |
| `cts.bend` | CBC-CS3 ciphertext stealing over any block cipher, on bytes |
| `xcbc.bend` | XCBC-MAC over any block cipher as a MAC |
| `vmac.bend` | VMAC (64- and 128-bit tags) over any 128-bit block cipher as a MAC |
| `hmac.bend` | HMAC over any hash: one call, or in pieces |
| `hkdf.bend` | HKDF over any hash: extract, expand, derive |
| `inst_cm.bend` | the adapter for cipher-modes: `CmError` onto `CrError`, and the format of its 128-bit block `CmBlock` |
| `inst_aes.bend` | AES as a block cipher (the only file importing cipher-modes' `aes.bend`, and so bend-collections) |
| `inst_cmac.bend` | CMAC over any 128-bit block cipher as a MAC |
| `inst_ccm.bend` | CCM over any 128-bit block cipher as an AEAD |
| `inst_lc.bend` | the adapter for legacy-ciphers: `LcError` onto `CrError`, its key schedules as `~key`, the XOR of its 64-bit block |
| `inst_rc4.bend` | RC4 and RC4-drop[n] as stream ciphers |
| `inst_crc.bend` | CRC-32 and CRC-64 of any parameter set as hashes |
| `inst_sha2.bend` | SHA-256 and SHA-512 as hashes: the adapter for bend-collections' SHA-2, its state wrapped in `CrSha2State` and its bytes converted to and from Octets |
| `inst_sha3.bend` | SHA3-256 as a hash: the adapter for bend-collections' SHA-3, its state wrapped in `CrSha3State` (block size 136, the SHA3-256 rate) |
| `pbkdf2.bend` | PBKDF2 over any MAC (RFC 8018): the checked derivation, the KDF interface's `~derive`, and the unchecked stream |
| `inst_pbkdf2.bend` | PBKDF2-HMAC-SHA-256 and PBKDF2-HMAC-SHA-1 |
| `kbkdf.bend` | the SP 800-108 KDFs over any MAC: counter and feedback mode, checked, as the KDF interface's `~derive`, and the unchecked streams |
| `inst_kbkdf.bend` | KBKDF-HMAC-SHA-256 in counter and feedback mode (32-bit counter and [L]_2) |
| `inst_michael.bend` | Michael (hashes/michael.bend) as a MAC: its key error mapped onto `CrError` |
| `gen/instances.py` | the table of instances and the law schemas: writes the per-instance laws in `LAWS.bend` and their proofs in `PROOF.bend` (`--check` checks they are up to date) |
| `gen/proof.py` | writes the lemmas proved on a word's 32 bits (the "bits" region of `PROOF.bend`) |

Bend imports do not re-export, so import the files you use: a program that
needs HMAC over its own hash imports `hash.bend`, `mac.bend` and
`hmac.bend`, and none of the instances. The generated regions lie between
`# BEGIN GENERATED by gen/<script>.py: <name>` and `# END GENERATED:
<name>` lines; everything else is written by hand.

## The interfaces

An interface is a signature of template arguments. An algorithm satisfies it
by supplying a def of each type; a generic algorithm takes the signature as
its own template arguments, specialised at compile time for each algorithm
it runs over, and takes only the arguments it uses. Every key, IV and length
an interface refuses is refused with a `CrError`, so code that mixes
algorithms handles one error type.

**Block cipher** (`block.bend`)

```
~K: Data                                          the key schedule
~Blk: Data                                        a block
~bsize: Nat                                       the block size in bytes
~key: B.Octets -> Result<&2, &2, CrError, K>      the key schedule of a raw key (CrBadKeyLength)
~enc: K -> Blk -> Blk                             encrypt one block
~dec: K -> Blk -> Blk                             decrypt one block
~blk_of: B.Octets -> Maybe<&2, Blk>               bsize bytes as a block
~blk_to: Blk -> B.Octets                          a block's bytes
~bxor: Blk -> Blk -> Blk                          XOR of two blocks
```

**Stream cipher** (`stream.bend`)

```
~S: Data                                          the state (key, IV, position)
~O: Data                                          one step's result
~start: B.Octets -> B.Octets -> Result<&2, &2, CrError, S>   key and IV
~update: S -> B.Octets -> O                       the next piece, encrypted or decrypted
~out_state: O -> S
~out_data: O -> B.Octets
```

Keystream generation is the extension point: `CrXor.update(~S, ~next, s, m)`
makes a stream cipher of any `~next: S -> CrKsStep<S>` (the next keystream
byte and the state after it), with `CrXor.out_state` and `CrXor.out_data`.

**Hash** (`hash.bend`)

```
~H: Data, ~bsize: Nat, ~dsize: Nat                the state, block size (HMAC's B), digest size
~init: H                                          the state before any byte
~update: H -> B.Octets -> H
~final: H -> B.Octets
~digest: B.Octets -> B.Octets                     one-shot
```

**MAC** (`mac.bend`)

```
~K: Data, ~key: B.Octets -> Result<&2, &2, CrError, K>
~compute: K -> B.Octets -> B.Octets
~verify: K -> B.Octets -> B.Octets -> Bool
```

**AEAD** (`aead.bend`)

```
~K: Data, ~key: B.Octets -> Result<&2, &2, CrError, K>
~seal: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, CrError, B.Octets>   nonce, aad, plaintext
~open: K -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, CrError, B.Octets>   nonce, aad, ciphertext with tag
```

**KDF** (`kdf.bend`): `~derive: B.Octets -> B.Octets -> B.Octets -> Nat ->
Result<&2, &2, CrError, B.Octets>` (secret, salt, info, length). A KDF with
other parameters takes them as template arguments first: PBKDF2's
iteration count (`~c`), its MAC and tag length; it has no context, so it
ignores info.

**Signature** (`sign.bend`): `~SK`, `~PK`, `~secret: B.Octets -> Result<..,
SK>`, `~public: SK -> PK`, `~pk_of: B.Octets -> Result<.., PK>`, `~pk_to: PK
-> B.Octets`, `~sign: SK -> B.Octets -> B.Octets`, `~verify: PK -> B.Octets
-> B.Octets -> Bool`.

**Key agreement** (`kex.bend`): `~SK`, `~PK`, `~secret`, `~public`,
`~pk_of`, `~pk_to` as for signatures, and `~shared: SK -> PK -> Result<..,
B.Octets>`.

The interface laws, as each file's header states them:

| Interface | Law | Statement |
|---|---|---|
| block cipher | round_trip | `dec(k, enc(k, b)) == b` for every key schedule and block |
| | round_trip_dual | `enc(k, dec(k, b)) == b` (where the cipher proves it) |
| | format | `blk_of(blk_to(b)) == Some{b}` |
| | xor | `bxor(bxor(a, b), b) == a` |
| | key_length | a key of a length the cipher does not take is refused |
| stream cipher | involution | `out_data(update(s, out_data(update(s, m)))) == m` |
| | streaming_data, streaming_state | `a ++ b` is `a`, then `b` from the state after `a` |
| hash | streaming | `update(s, a ++ b) == update(update(s, a), b)` for every state |
| | split | `final(update(update(init, a), b)) == digest(a ++ b)`: streaming equals one-shot for every split |
| | length | `final(s)` has `dsize` bytes |
| MAC | accepts | `verify(k, m, compute(k, m)) == True` |
| | agrees | `verify(k, m, t) == B.Octets.is_eq(compute(k, m), t)`: exactly the computed tag |
| AEAD | round_trip | `bind(seal(k, n, a, p), c => open(k, n, a, c)) == map(c => p, seal(k, n, a, p))`: open accepts what seal produced, and refuses alike when seal refuses |
| | tamper | a changed tag, ciphertext or associated data is refused (`CrTagMismatch`) |
| KDF | length, prefix | a derivation gives the length asked for; a shorter one is a prefix of a longer |
| signature | accepts, pk_format | `verify(public(sk), m, sign(sk, m)) == True`; `pk_of(pk_to(p)) == Done{p}` |
| key agreement | agree, pk_format | `shared(a, public(b)) == shared(b, public(a))`; as above |

## How the laws are stated, and why --verdict accepts them

A law cannot take an algorithm's property as a template hypothesis: the
BendTT kernel behind `--verdict` has no model of a template whose type is a
proposition (`~inv: @k -> @b -> {dec(k, enc(k, b)) == b}`), which is why
cipher-modes' four round-trip laws fail `--verdict`. An ordinary hypothesis
(`inv: ...`) is modelled, but it is affine: a function value is not `Data`,
so it cannot be `+inv`, and an induction cannot use it at every step. So the
laws come in three forms:

* **Generic laws** need nothing from the algorithm but its type, and are
  stated once over the template arguments: CTR's three stream laws for every
  block cipher (from `CrXor`'s, for every keystream generator), the MAC
  default verify's two laws for every `~compute` (so HMAC over any hash and
  CMAC over any cipher accept what they compute), the CRC hash laws for every
  parameter set.
* **Conditional laws** take the algorithm's property at the very arguments
  they need, as an ordinary hypothesis used once (`--verdict` accepts these):
  `lift_round_trip` (an AEAD's round trip survives mapping its errors onto
  `CrError`), `ccm_round_trip_if`, `sign_verify_bytes_if`, `kex_agree_if`.
* **Law schemas, instantiated per instance.** A law whose proof needs the
  algorithm's property at every step of an induction (ECB and CBC undo
  themselves because the cipher does, block by block; HMAC in pieces because
  the hash streams) is a schema in `gen/instances.py`: a statement and a
  proof with the instance's defs and the name of the law its own package
  proves filled in. The script writes one law and one proof per instance;
  there the property is a call of a global law, which may be used any number
  of times.

Every law is about the public interface, and the proofs use other packages
only through their laws (bytes', crc's, legacy-ciphers'), except where a
lemma computes on a word's 32 symbolic bits, as the other packages' proofs
do.

## The instances

Each instance is a tuple of existing defs (with the adapters'
`CrLc.key`/`CrCm.key`, which map an algorithm's errors onto `CrError`);
the files above give each one's tuple. For example SM4 as a block cipher:

```
~S.LcSm4Key, ~M.CmBlock, ~16n, ~LC.CrLc.key(~S.LcSm4Key, ~S.LcSm4.key),
~S.LcSm4.encrypt, ~S.LcSm4.decrypt,
~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ~CM.CrBlk128.xor
```

and then CBC over it is `Md.CrCbc.encrypt(~S.LcSm4Key, ~M.CmBlock, ~16n,
~S.LcSm4.encrypt, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets,
~CM.CrBlk128.to_octets, k, iv, m)`, and CTR over it a stream cipher whose
`~update` is `~Md.CrCtr.update(~S.LcSm4Key, ~M.CmBlock, ~S.LcSm4.encrypt,
~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets)`.

A hash of the hashes package plugs in with its own defs, no adapter: MD5
is `~Hs.HsMdState<Hs.HsW4>, ~64n, ~16n, ~HM5.HsMd5.init(), ~HM5.HsMd5.update,
~HM5.HsMd5.final, ~HM5.HsMd5.digest`, and each of its files' headers gives
its tuple. Michael as a MAC is `~Hs.HsW2, ~CrMichael.key,
~HMI.HsMichael.mic, ~CrMichael.verify`; PBKDF2 over HMAC-SHA-256 with c
iterations, as a KDF, is `~Pb.CrPbkdf2.derive(~Hm.CrHmacKey,
~Hm.CrHmac.key_of(~64n, ~SH.CrSha2.sha256), ~Hm.CrHmac.mac(~SH.CrSha2.sha256),
~32n, ~c)`.

| Instance | Interface | Proved | Tested |
|---|---|---|---|
| DES, 3DES (64-bit, `LcBlock64`) | block cipher | round_trip, round_trip_dual (from legacy-ciphers), format (legacy-ciphers'), xor, key_length; ECB and CBC round trips over it | vectors both ways, ECB/CBC/CTR vs cryptography |
| SM4, Camellia, Serpent, Twofish (128-bit, `CmBlock`) | block cipher | the same | vectors both ways; ECB/CBC/CTR vs cryptography (SM4, Camellia) or legacy-ciphers' models (Serpent, Twofish) |
| ARIA, CAST-256 (128-bit, `CmBlock`) | block cipher | the same (from legacy-ciphers' `aria_round_trip`, `cast6_round_trip` and their duals) | RFC 5794 and RFC 2612 vectors both ways; ECB/CBC/CTR vs the openssl command (ARIA) or legacy-ciphers' model (CAST-256) |
| Blowfish, CAST-128, TEA, XTEA, FCrypt (64-bit, `LcBlock64`) | block cipher | the same | vectors both ways (the set Schneier publishes, RFC 2144 B.1, the FCrypt specification's; TEA and XTEA on the model's values: their papers give none); ECB/CBC/CTR vs cryptography (Blowfish, CAST-128) or the model (TEA, XTEA, FCrypt) |
| PCBC over every block cipher whose round trip is proved | (mode) | `<c>_pcbc_round_trip` on blocks, for every key, IV and list of blocks | the FCrypt specification's PCBC vector; vs `ref/gen.py`'s PCBC over every cipher (AES included) |
| LRW over every 128-bit block cipher whose round trip is proved | (mode) | `<c>_lrw_round_trip` on blocks, for every key, tweak key, first index and list of blocks | IEEE P1619 Annex B vectors 1 to 5 (AES-128 and AES-256) both ways; vs the Linux kernel's lrw(aes) through AF_ALG, and `ref/gen.py`'s LRW over the others |
| CBC-CS3 over every block cipher | (mode) | none (below) | RFC 3962 B's four vectors both ways and a short message refused; vs the kernel's cts(cbc(aes)), and `ref/gen.py`'s CS3 over the others |
| XCBC-MAC over every block cipher | MAC | `xcbc_accepts` (every cipher) | RFC 3566 test cases 1 to 7; vs `ref/gen.py`'s XCBC over AES, SM4, Camellia, Serpent, Twofish, ARIA, CAST-256; a changed tag refused |
| VMAC over every 128-bit block cipher | MAC | `vmac_accepts` (every cipher and nonce length) | draft-krovetz-vmac-01's vectors (64- and 128-bit tags); vs `ref/gen.py`'s VMAC over the 128-bit ciphers, nonces of 1 to 15 bytes; a changed tag refused |
| AES-128, AES-256 (`CrAes.key`; `CrAes.key_enc` without the decryption round keys) | block cipher | format, xor, key_length; FIPS 197 C.1 through the interface | round_trip (cipher-modes tests AES decryption but proves no law about it); C.1 and C.3 both ways; ECB/CBC/CTR vs cryptography |
| CTR over every block cipher above | stream cipher | involution, streaming_data, streaming_state, for every block cipher | SP 800-38A F.5.1; in two pieces vs cryptography / models, a counter wrapping |
| RC4, RC4-drop[n] | stream cipher | involution, streaming_data, streaming_state (from legacy-ciphers); key and IV refusals | RFC 6229 whole and in pieces, drop[1536]; vs cryptography's ARC4 and the model |
| CMAC over every 128-bit cipher above | MAC | accepts, agrees (for every cipher) | RFC 4493 examples 1 to 4; vs cryptography (AES, SM4, Camellia) and RFC 4493 over the models; a changed tag refused |
| CCM over every 128-bit cipher above, any tag length | AEAD | round_trip given cipher-modes' `ccm_round_trip` (below) | RFC 3610 packets 1 to 3; vs cryptography's AESCCM, and RFC 3610 over the others; changed tag, ciphertext and associated data refused |
| CRC-32 of any parameter set (CRC-32, CRC-32C, ...) | hash | streaming, split (for every parameter set), length; check values | vs binascii.crc32 and a Rocksoft-model CRC-32C, in pieces |
| CRC-64 of any parameter set (CRC-64/XZ, ...) | hash | streaming, split; check value | length; vs a Rocksoft-model CRC-64/XZ, in pieces |
| SHA-256, SHA-512 (bend-collections; `CrSha2State`) | hash | the one-shot digest is FIPS 180-4's executable specification (bend-collections-laws-crypto's spec); split into two and three pieces equals one-shot; length; SHA-256 of "abc" | streaming for every state (bend-collections proves pieces only from the start); FIPS 180-4's examples whole and in pieces; vs hashlib, in pieces |
| SHA3-256 (bend-collections; `CrSha3State`) | hash | the one-shot digest is FIPS 202's executable specification (bend-collections-laws-crypto's spec); split into two and three pieces equals one-shot; length; SHA3-256 of "abc" | streaming for every state (as for SHA-2); NIST's examples whole and in pieces; vs hashlib, in pieces |
| HMAC over each hash above | MAC | accepts, agrees (for every hash); split (in pieces equals one call) over CRC-32, CRC-64, SHA-256, SHA-512 and SHA3-256; streaming of HMAC's state over CRC-32 and CRC-64; RFC 4231 test case 2 for HMAC-SHA-256; one HMAC-CRC-32 vector | RFC 4231 test cases 1 to 7 for HMAC-SHA-256 and HMAC-SHA-512; vs Python's hmac over hashlib's SHA-256, SHA-512 and SHA3-256 and over CRC-32, CRC-32C and CRC-64/XZ, keys from 0 to 200 bytes |
| HKDF over each hash above (HKDF-SHA-256 the named one) | KDF | the refusal of more than 255 digests (over CRC-32 and SHA-256) | RFC 5869 A.1 to A.3; length; vs cryptography's HKDF over SHA-256, SHA-512 and SHA3-256, and RFC 5869 on Python's hmac over the CRCs |
| MD4, MD5, SHA-1, RIPEMD-160, SM3, Streebog-256, Streebog-512 (hashes; `Hs.HsMdState<C>`) | hash | streaming for every state, split, split3, length for every state (from hashes' laws, `gen/instances.py`'s `hs_row`s); their vectors in hashes | the specifications' vectors in hashes; one-shot and in pieces through the interface (check.bend); vs hashlib (MD5, SHA-1, RIPEMD-160, SM3) and hashes' models (MD4, Streebog) |
| HMAC over each of those | MAC | accepts, agrees; streaming of HMAC's state and split (in pieces equals one call), for each | RFC 2202 test cases 1 and 2 for HMAC-MD5 and HMAC-SHA-1, in pieces with verify; HMAC over the others vs Python's hmac (over hashlib or hashes' models), keys of 0 to 100 bytes |
| Michael (hashes; `Hs.HsW2`, `CrMichael.key`) | MAC | accepts (for every key and message), agrees (the named default verify), the refusal of a 16-byte key; the sixth vector through `CrMac.compute_with` (the vectors are unverified against a published copy of 802.11i: hashes/README.md) | the six vectors through the interface, verify accepting and refusing a changed tag, a 7-byte key refused; vs hashes' model |
| PBKDF2 over any MAC (`CrPbkdf2.pbkdf2`, `.derive`; PBKDF2-HMAC-SHA-256 and -SHA-1 the named ones) | KDF | length (a derivation that succeeds has the length asked, for every MAC and input); the stream's length and prefix laws (for every MAC and input); the refusal of 0 iterations; RFC 6070 test cases 1 and 2, the first 32 bytes of RFC 7914's c = 1 | RFC 6070 cases 1 to 3, 5 and 6 and RFC 7914's two in full (c = 80000 among them); PBKDF2 over HMAC-MD5 through the KDF interface; vs hashlib.pbkdf2_hmac over SHA-1, SHA-256, MD5, RIPEMD-160 and SM3, and cryptography's PBKDF2HMAC for SHA-1 and SHA-256 |
| SP 800-108 KDFs over any MAC (`CrKbkdf.counter_kdf`, `.feedback_kdf`, `.derive`; KBKDF-HMAC-SHA-256 in counter and feedback mode the named ones) | KDF | length (a derivation that succeeds has the length asked, for every MAC and input, both modes); the streams' length and prefix laws (both modes, for every MAC and input); KBKDF-HMAC-SHA-256 in counter mode on a cryptography value | counter and feedback mode over HMAC-SHA-256, and a refusal (check.bend); vs cryptography's KBKDFHMAC (counter mode, SHA-1 and SHA-256) and `ref/gen.py`'s SP 800-108 (feedback mode, and SM3) |

**CCM.** cipher-modes proves `ccm_round_trip` for every cipher, key, tag
length, nonce, associated data and message; `ccm_round_trip_if` here proves
the AEAD round trip of `CrCcm.seal` and `CrCcm.open` from it, at the same
arguments. The two are not joined in `PROOF.bend` because a proof that
imports cipher-modes' `PROOF.bend` takes in its four laws with a template
hypothesis, and then fails `--verdict` as cipher-modes does; joined, they
are the AEAD round trip for every CCM instance.

**Not instances.** XXH64 (zstd) fits the hash interface's shape, but zstd
proves no streaming law for it, and one would need zstd's internals, so it
is not an instance yet. The signature and key-agreement interfaces' instances
(RSA, DH, ECDSA, ECDH, SM2, EC-RDSA) are in bend-osdev-pubkey, with their
interface laws written out per instance there: here, `sign_verify_bytes_if`
and `kex_agree_if` prove that the generic helpers keep the laws for every
scheme. bend-collections also has Ed25519, X25519 and ChaCha20-Poly1305,
which would plug in through adapters like `inst_sha2.bend` (not done in
this version).

**Where SHA-2 and SHA-3 come from.** The code is bend-collections@1.0.0.0's
`src/crypto/hash.bend` and the `sha`, `sha512`, `sha3` and `keccak` files
it imports. `inst_sha2.bend` imports it from
bend-collections-laws-crypto@1.0.0.0, which ships the same files (checked
file by file; it lacks only keccak's unused `hex.bend`) together with their
proofs (`Split.sha256`, `Incremental.sha256`, `Sha256.length`,
`Sha256.value`, and the same for SHA-512 and SHA3-256). `inst_sha3.bend`
imports the same file for SHA3-256. Bend names a def by the package
it comes from, so those laws hold of that package's copy and not of
bend-collections@1.0.0.0's: importing the copy they are about is what lets
`LAWS.bend` cite them.

**Why the cipher-modes adapter is here.** `inst_cm.bend`, `inst_aes.bend`,
`inst_cmac.bend` and `inst_ccm.bend` adapt cipher-modes to the interfaces
from this package, not from cipher-modes: the dependency then runs one way
(crypto on the algorithm packages, never back), cipher-modes and
legacy-ciphers are unchanged, and the interface files themselves import
only bytes.

## Public interface

**`crypto.bend`**: `CrError` (`CrBadKeyLength{got}`, `CrBadIvLength{got}`,
`CrBadNonceLength{got}`, `CrBadTagLength{got}`, `CrBadBlockSize{got}`,
`CrNotBlockMultiple{len}`, `CrTooShort{len}`, `CrTooLong{len}`,
`CrBadPadding{}`, `CrTagMismatch{}`, `CrBadOutputLength{got}`, `CrBadKey{}`,
`CrBadPublicKey{}`), `CrError.check(ok, e)`, `CrError.lift(~E, ~A, ~f, r)`.

| File | Defs and types |
|---|---|
| `block.bend` | `CrBlockCipher.encrypt_octets`, `CrBlockCipher.decrypt_octets` (one block of bytes, `CrBadBlockSize`), `CrBlockCipher.encrypt_with` (a raw key, then a block) |
| `stream.bend` | `CrStream.crypt` (key, IV, data in one call), `CrStream.keystream`; `CrKsStep<S>{k, st}`, `CrKsStep.k`, `CrKsStep.st`; `CrXorOut<S>{state, data}`; `CrXor.update`, `CrXor.out_state`, `CrXor.out_data` |
| `hash.bend` | `CrHash.update_all`, `CrHash.of_pieces`, `CrHash.digest_of` (the streaming form as a one-shot `~digest`) |
| `mac.bend` | `CrMac.verify_tag` (the named default `~verify`), `CrMac.compute_with` |
| `aead.bend` | `CrAead.seal_with`, `CrAead.open_with` |
| `kdf.bend` | `CrKdf.derive_key` |
| `sign.bend` | `CrKeypair<SK, PK>{secret, public}`, `CrSign.keypair`, `CrSign.verify_bytes` |
| `kex.bend` | `CrKex.agree` |
| `modes.bend` | `CrEcb.encrypt_blocks`, `CrEcb.decrypt_blocks`, `CrCbc.encrypt_blocks`, `CrCbc.decrypt_blocks` (blocks; CBC's last block is the next call's IV); `CrModes.blocks_of` (`CrNotBlockMultiple`), `CrModes.octets_of`; `CrEcb.encrypt`, `CrEcb.decrypt`, `CrCbc.encrypt`, `CrCbc.decrypt` (bytes, whole blocks, a one-block IV); `CrCtrState<K>`, `CrCtr.start` (a one-block initial counter, `CrBadIvLength`), `CrCtr.next`, `CrCtr.update` |
| `octets.bend` | `CrOct.xor`, `CrOct.rep`, `CrOct.pieces` |
| `pcbc.bend` | `CrPcbc.encrypt_blocks`, `CrPcbc.decrypt_blocks`, `CrPcbc.next_iv` (the chaining value after a list of blocks); `CrPcbc.encrypt`, `CrPcbc.decrypt` (bytes, whole blocks, a one-block IV) |
| `lrw.bend` | `CrLrwKey<K>{k, t}`, `CrLrw.key` (the cipher's key then a 16-byte tweak key), `CrLrw.encrypt_blocks`, `CrLrw.decrypt_blocks` (from a first index), `CrLrw.encrypt`, `CrLrw.decrypt` (bytes; the IV is the first block's 16-byte big-endian index) |
| `cts.bend` | `CrCts.encrypt`, `CrCts.decrypt` (any length of at least one block, `CrTooShort` below; a one-block IV) |
| `xcbc.bend` | `CrXcbcKey<K>`, `CrXcbc.key`, `CrXcbc.mac`, `CrXcbc.mac96` (RFC 3566's 96-bit tag), `CrXcbc.verify` |
| `vmac.bend` | `CrVmacKey<K>`, `CrVmac.key` (`~words`: 1 for VMAC-64, 2 for VMAC-128), `CrVmac.tag` (a nonce of 1 to bsize - 1 bytes, `CrBadNonceLength`), `CrVmac.mac` (`~nlen`: the message's first nlen bytes are the nonce), `CrVmac.verify` |
| `hmac.bend` | `CrHmacKey{ipad, opad}`, `CrHmacState<H>`, `CrHmac.key`, `CrHmac.key_of`, `CrHmac.mac`, `CrHmac.verify`, `CrHmac.start`, `CrHmac.update`, `CrHmac.finish` |
| `hkdf.bend` | `CrHkdf.extract`, `CrHkdf.expand` (`CrBadOutputLength` past 255 digests), `CrHkdf.derive` |
| `inst_cm.bend` | `CrCm.err`, `CrCm.lift`, `CrCm.key`; `CrBlk128.of_octets`, `CrBlk128.to_octets`, `CrBlk128.xor` |
| `inst_lc.bend` | `CrLc.err`, `CrLc.lift`, `CrLc.key`; `CrBlk64.xor` |
| `inst_aes.bend` | `CrAes.key`, `CrAes.key_enc` |
| `inst_cmac.bend` | `CrCmac.mac`, `CrCmac.verify` |
| `inst_ccm.bend` | `CrCcm.seal`, `CrCcm.open` |
| `inst_rc4.bend` | `CrRc4.start`, `CrRc4.start_drop` |
| `inst_crc.bend` | `CrCrc32.init`, `.update`, `.final`, `.digest`; `CrCrc64.init`, `.update`, `.final`, `.digest` (each with `~spec`) |
| `inst_sha2.bend` | `CrSha2State` (opaque), `CrSha2.init256`, `CrSha2.init512`, `CrSha2.update`, `CrSha2.final`, `CrSha2.sha256`, `CrSha2.sha512` |
| `inst_sha3.bend` | `CrSha3State` (opaque), `CrSha3.init`, `CrSha3.update`, `CrSha3.final`, `CrSha3.sha3_256` |
| `pbkdf2.bend` | `CrPbkdf2.pbkdf2` (password, salt, iteration count as a `U32`, length; `CrTooShort{0}` for 0 iterations, `CrBadOutputLength{n}` past (2^32 - 1) hLen bytes or for hLen 0, and the MAC's own refusal of the password), `CrPbkdf2.derive` (the KDF interface's `~derive`, with `~c`), `CrPbkdf2.stream` (the first n bytes from a prepared key, unchecked) |
| `inst_pbkdf2.bend` | `CrPbkdf2.hmac_sha256`, `CrPbkdf2.hmac_sha1` |
| `kbkdf.bend` | `CrKbkdf.counter_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, label, context, n)`, `CrKbkdf.feedback_kdf(.., ki, iv, label, context, n)` (`CrBadOutputLength` for more than 2^(8 rlen) - 1 blocks in counter mode or 2^32 - 1 in feedback mode, or an L that does not fit llen bytes; the MAC's own refusal of K_IN), `CrKbkdf.derive` (the KDF interface's `~derive` in counter mode: secret K_IN, salt the Label, info the Context), `CrKbkdf.counter_stream`, `CrKbkdf.feedback_stream` (the first n bytes from a prepared key, unchecked), `CrKbkdf.counter(rlen, i)`, `CrKbkdf.length(llen, n)`, `CrKbkdf.fixed(~llen, label, context, n)` |
| `inst_kbkdf.bend` | `CrKbkdf.hmac_sha256_counter(ki, label, context, n)`, `CrKbkdf.hmac_sha256_feedback(ki, iv, label, context, n)` |
| `inst_michael.bend` | `CrMichael.err`, `CrMichael.key`, `CrMichael.verify` |

Everything else (`cr.*`, `CrKsRun`) is internal. A def that is an
interface's argument takes no `+` parameter (`@+x: A -> ...` is a different
type from `@x: A -> ...`).

## Extension points

* **A new algorithm plugs in** by supplying defs of an interface's types: a
  key schedule answering `Result<&2, &2, CrError, K>` (an algorithm with its
  own error type maps it with `CrError.lift`, as `CrLc.key` and `CrCm.key`
  do), and the interface's functions, none taking a `+` parameter. Then:
  1. a row in `gen/instances.py` (`BLOCK`, `STREAM` or `HASH`) with its
     defs and the names of the laws its own package proves (for a block
     cipher, decryption undoes encryption; for a hash, split and split3, and
     streaming where it has one);
  2. `python3 gen/instances.py`: it writes the instance's laws (round trip,
     key length, ECB and CBC round trips; or the stream laws; or HMAC in
     pieces) and their proofs;
  3. its vectors in `check.bend` and its cases in `ref/gen.py`.
  A cipher of a new block size brings its block format (`~blk_of`,
  `~blk_to`, `~bxor`, and their two laws, as `inst_cm.bend` does for
  `CmBlock`).
* **A new generic algorithm** takes the signature's template arguments it
  uses. A law it needs from the algorithm becomes a schema in
  `gen/instances.py` (a function writing a statement and a proof, given an
  instance's row), or a conditional law if it uses the property once.
* **Keystream generators:** any `~next: S -> CrKsStep<S>` is a stream cipher
  through `CrXor`, with its three laws already proved (as CTR is).
* **PBKDF2's PRF** is any MAC (`~K`, `~key`, `~compute`) with its tag
  length `~hlen`: HMAC over any hash is the usual one (`inst_pbkdf2.bend`
  writes two), CMAC over a block cipher or Michael another; its length and
  prefix laws hold for every one. **The SP 800-108 KDFs** take the same
  MAC, and the counter's and [L]_2's widths (`~rlen`, `~llen`, in bytes;
  `~rlen` 0 leaves the counter out in feedback mode); `inst_kbkdf.bend`'s
  pair is HMAC-SHA-256 with 32-bit fields.
* **Named defaults that can be replaced:** the MAC verify
  (`CrMac.verify_tag`, a comparison of every byte), HMAC's block size for a
  hash without one (64 for the CRCs), AES's key schedule with or without
  the decryption round keys, the CRC parameter set (`~spec`, any
  `Crc32Spec` or `Crc64Spec`).

## Laws

`LAWS.bend` has 208 laws.

**Generic, for every input and every algorithm of the shape:**
`xor_involution`, `xor_streaming_data`, `xor_streaming_state` (CrXor, every
keystream generator); `ctr_involution`, `ctr_streaming_data`,
`ctr_streaming_state` (CTR, every block cipher); `cmblock_format`,
`cmblock_xor`, `lcblock64_format`, `lcblock64_xor` (the two block formats);
`mac_verify_tag_accepts`, `mac_verify_tag_agrees`, `hmac_accepts` (every
hash), `cmac_accepts` (every 128-bit cipher), `xcbc_accepts` (every block
cipher), `vmac_accepts` (every block cipher and nonce length); `crc32_hash_streaming`,
`crc32_hash_split`, `crc32_hash_split3`, `crc32_hash_length`,
`crc64_hash_streaming`, `crc64_hash_split`, `crc64_hash_split3` (every
parameter set); `sha256_spec`, `sha256_hash_split`, `sha256_hash_split3`,
`sha256_hash_length` and the same for SHA-512 and SHA3-256 (every
message), from
bend-collections-laws-crypto's laws; `michael_accepts` (every key and
message); `pbkdf2_length` (every MAC, password, salt, iteration count and
length: a derivation that succeeds has the length asked for),
`pbkdf2_stream_length` and `pbkdf2_stream_prefix` (the first n bytes of a
longer stream are the stream of n bytes): the KDF interface's length and
prefix laws for PBKDF2. They hold because the output is generated a byte
at a time, each block computed when the bytes before it are used up, so
neither needs the MAC's tag length nor any arithmetic on ceilings. The same
for SP 800-108: `kbkdf_counter_stream_length`, `kbkdf_counter_stream_prefix`,
`kbkdf_feedback_stream_length`, `kbkdf_feedback_stream_prefix` (every MAC,
key, fixed input, IV and length) and `kbkdf_counter_length`,
`kbkdf_feedback_length` (a derivation that succeeds has the length asked
for). The interface's prefix law holds of the streams, not of the
derivations: a derivation binds its length L into every PRF input, so
derivations of two lengths differ (as SP 800-108 intends).

**Conditional** (a property of the algorithm at the arguments used, as a
hypothesis): `lift_round_trip`, `ccm_round_trip_if`,
`sign_verify_bytes_if`, `kex_agree_if`.

**Per instance** (generated): `<c>_block_round_trip`,
`<c>_block_round_trip_dual`, `<c>_ecb_round_trip`, `<c>_cbc_round_trip`,
`<c>_pcbc_round_trip` for c = des, tdes, sm4, camellia, serpent, twofish,
aria, cast6, blowfish, cast5, tea, xtea, fcrypt; `<c>_lrw_round_trip` for
the 128-bit ones among them (sm4, camellia, serpent, twofish, aria, cast6);
`<c>_key_length` for those and aes, aes_enc; `rc4_stream_involution`,
`rc4_stream_streaming_data`, `rc4_stream_streaming_state`;
`hmac_crc32_streaming`, `hmac_crc32_split`, `hmac_crc64_streaming`,
`hmac_crc64_split` (every parameter set), `hmac_sha256_split`,
`hmac_sha512_split`, `hmac_sha3_256_split` (the hash rows in `gen/instances.py`: HMAC in pieces
follows from the hash's split laws, and HMAC's state in pieces from its
streaming law where it has one); for h = md4, md5, sha1, ripemd160, sm3,
streebog256 and streebog512 (the `hs_row`s), the hash interface's laws
`<h>_hash_streaming` (every state), `<h>_hash_split`, `<h>_hash_split3` and
`<h>_hash_length` (every state), each the hashes package's law, and
`hmac_<h>_streaming`, `hmac_<h>_split`.

**Vectors** (proved by computation): the CRC-32, CRC-32C and CRC-64/XZ
check values through the hash interface; SHA-256 of "abc" (FIPS 180-4);
SHA3-256 of "abc" (FIPS 202, NIST's examples);
HMAC-SHA-256 on RFC 4231's test case 2; HMAC over CRC-32 (Python's hmac's
value); Michael's sixth vector through the MAC interface and its refusal
of a 16-byte key; PBKDF2-HMAC-SHA1 on RFC 6070's test cases 1 and 2, the
first 32 bytes of PBKDF2-HMAC-SHA256 on RFC 7914's first vector (all 64
bytes, two blocks, run past `--verdict`'s kernel fuel: check.bend computes
them), and PBKDF2's refusal of 0 iterations; KBKDF-HMAC-SHA-256's counter-mode
stream, 32 bytes (`kbkdf_hmac_sha256_vector`, cryptography's KBKDFHMAC's
value; stated on the stream because the derivation's length checks compare
with 2^32, which `--verdict`'s kernel cannot compute); FIPS 197 C.1 through the
block-cipher interface (with `CrAes.key_enc`: with `CrAes.key`, whose
decryption round keys the kernel then evaluates, the vector checks but
`--verdict` fails); the refusals (an empty RC4 key, an IV given to RC4, a
CTR counter of the wrong length, bytes that are not whole blocks, an HKDF
output past 255 digests, over CRC-32 and over SHA-256).

**Not proved, and tested:** AES's round trip (cipher-modes tests it and
proves no law), and so ECB, CBC, PCBC and LRW round trips over AES; the
CBC-CS3 round trip: decryption cuts the ciphertext into pieces again, so a
proof needs `CrOct.pieces` of a concatenation of encrypted blocks to give
those blocks back (every block's length through the format, the stolen
bytes' `take` and `drop`, the XOR with a zero-padded piece undone over its
length), for every block size; those lemmas are not done in this version,
and `PROOF.bend` already takes over 2 GB of the checker's memory under
`--verdict` (tested: RFC 3962's vectors both ways, and 32 cases against the
kernel's cts(cbc(aes)) and `ref/gen.py`'s CS3); the byte layer of PCBC and
LRW (as of ECB and CBC: the laws are on lists of blocks); VMAC's and XCBC's
values (the MAC laws hold whatever the tag is; the values are tested on
the specifications' vectors); the CCM round trip unconditionally (above);
an AEAD's and a MAC's refusal of changed input (a forgery succeeds with probability
2^-8tlen, so it is no law for every input; tested on every instance); the
KDF laws for HKDF (its length needs arithmetic on ceilings not done here;
PBKDF2's are proved, above); CRC-64's
digest length; SHA-2's and SHA3-256's streaming law for every state (bend-collections
proves the pieces from the start state only, which is what the split laws
and HMAC need); the byte layer of ECB and CBC (`CrModes.blocks_of` and
`octets_of` for every block size); the CTR counter's increment (the stream
laws hold whatever it is; its value is tested against SP 800-38A and
cryptography).

## Tests

* `check.bend` runs every instance through its interface on its
  specification's vectors: AES (FIPS 197 C.1, C.3), DES (SP 800-17), 3DES
  (SP 800-67), SM4, Camellia, Serpent, Twofish, each both ways; ECB, CBC and
  CTR over AES (SP 800-38A F.1.1, F.2.1, F.5.1), 3DES CBC (SP 800-67),
  DES CTR in pieces with the counter wrapping; RC4 (RFC 6229) whole, in
  pieces, and drop[1536]; CMAC (RFC 4493 examples 1 to 4) with a changed
  tag refused; CCM (RFC 3610 packets 1 to 3) sealed, opened, and a changed
  tag refused; the CRC check values, in pieces; HMAC and HKDF over CRC-32
  and CRC-64/XZ (values from Python's hmac); SM4 CBC over 32 KB and AES CTR
  over 32 KB both ways; the refusals; SHA-256 and SHA-512 on FIPS 180-4's
  examples, whole and in three pieces; HMAC-SHA-256 and HMAC-SHA-512 on RFC
  4231's test cases 1 to 7 (case 5 truncated to 128 bits), and
  HMAC-SHA-256 in pieces with verify; HKDF-SHA-256 on RFC 5869's A.1 to
  A.3; the hashes package's seven hashes through the hash interface, whole
  and in three pieces (values from hashlib and hashes' models); HMAC-MD5
  and HMAC-SHA-1 on RFC 2202's test cases 1 and 2, and HMAC over MD4,
  RIPEMD-160, SM3 and Streebog, each in pieces with verify; Michael's six
  vectors through the MAC interface, with verify and a 7-byte key refused;
  PBKDF2-HMAC-SHA1 on RFC 6070's test cases 1, 2, 3, 5 and 6 (case 4, 2^24
  iterations, would take minutes and is left out) and PBKDF2-HMAC-SHA256 on
  RFC 7914's two vectors (80,000 iterations in the second), 0 iterations
  refused, and PBKDF2 over HMAC-MD5 through the KDF interface;
  KBKDF-HMAC-SHA-256 in counter mode (cryptography's KBKDFHMAC's value)
  and in feedback mode (`ref/gen.py`'s SP 800-108's value), 42 bytes each,
  and an output too long for a one-byte counter refused. The SHA-2
  values are those of Python's hashlib, hmac and cryptography, which the
  script that wrote them first checked against the RFCs' published values;
  the new hashes' are the specifications' and hashlib's, the PBKDF2 and
  RFC 2202 values the RFCs' (which the script that wrote them checked
  against hashlib.pbkdf2_hmac and hmac); SHA3-256 on NIST's examples (the
  empty message, "abc", 200 bytes of a3, whole and in three pieces) and
  HMAC-SHA3-256 (Python's hmac's value). Then the newer ciphers: ARIA (RFC
  5794 A.1), CAST-256 (RFC 2612's 128-bit vector), Blowfish (a vector of
  the set Schneier publishes), CAST-128 (RFC 2144 B.1), TEA and XTEA (the
  model's values), FCrypt (its specification's) both ways; PCBC over FCrypt
  (the specification's PCBC vector); LRW-AES on IEEE P1619 Annex B's five
  vectors both ways; CBC-CS3 over AES on RFC 3962's 17-, 31-, 32- and
  64-byte vectors both ways, and a 13-byte message refused; AES-XCBC-MAC on
  RFC 3566's seven test cases; VMAC-AES on draft-krovetz-vmac-01's four
  messages with 64- and 128-bit tags.
* `ref/run.sh` compares every instance through its interface with
  implementations outside this package (499 cases: 187 against Python's
  cryptography, directly or through `ref/gen.py`'s modes over its block
  ciphers, and its PBKDF2HMAC and KBKDFHMAC; 22 against the openssl command's ARIA; 9
  against the Linux kernel's lrw(aes) and cts(cbc(aes)) through AF_ALG; 123
  against legacy-ciphers' `ref/model.py`, for Serpent, Twofish, CAST-256,
  TEA, XTEA, FCrypt, and RC4 at the key sizes cryptography lacks; 128
  against Python's `hashlib`, `hmac`, `binascii` and `gen.py`'s
  Rocksoft-model CRCs, and the refusals; 30 against hashes' `ref/model.py`,
  for MD4, Streebog and Michael, which Python lacks here): one block both
  ways for every block cipher and key size; ECB, CBC, CTR (in two pieces),
  PCBC and CBC-CS3 over every block cipher; LRW, XCBC-MAC and VMAC (64- and
  128-bit tags, nonces of 1 to 15 bytes) over the 128-bit ones; RC4 in two
  pieces for keys of 1 to 256 bytes;
  CMAC over five ciphers with verify; CCM over five ciphers with every tag
  length, changed tag, ciphertext and associated data refused; SHA-256,
  SHA-512, SHA3-256 and the three CRC hashes in pieces; HMAC over all six
  (keys of 0 to 200 bytes, in pieces, verify); HKDF over SHA-256, SHA-512
  and SHA3-256 (against cryptography's HKDF) and over CRC-32 and CRC-64/XZ; the hashes package's
  seven hashes in pieces and HMAC over them (keys of 0 to 100 bytes);
  Michael with verify accepting its tag and refusing it changed; PBKDF2
  over HMAC over SHA-1, SHA-256, MD5, RIPEMD-160 and SM3 (1 to 40
  iterations, outputs of one byte to three blocks and more) against
  hashlib.pbkdf2_hmac, and cryptography's PBKDF2HMAC for SHA-1 and SHA-256;
  the SP 800-108 KDFs over HMAC over SHA-1, SHA-256 and SM3 in counter mode
  (cryptography's KBKDFHMAC for SHA-1 and SHA-256, counter and L fields of
  1, 2 and 4 bytes) and feedback mode, with and without the counter
  (`gen.py`'s SP 800-108, checked first against KBKDFHMAC in counter mode),
  outputs of one byte to three blocks and more.
  `gen.py` first checks its own CTR, CMAC and CCM against cryptography for AES, its HKDF against
  cryptography's HKDF on RFC 5869's test case 1, and its CRCs against the
  catalogue's check values; its PCBC, LRW, CS3, XCBC and VMAC on the
  specifications' vectors above, and its LRW and CS3 against the kernel's
  (when AF_ALG has them; the cases fall back to `gen.py`'s modes when it
  does not). **legacy-ciphers' models share an author with that package**:
  Serpent, Twofish, CAST-256, TEA, XTEA and FCrypt are compared with them
  alone. So do **hashes' models with the hashes package**: MD4, Streebog
  and Michael are compared with them alone (after the models are checked
  against the specifications' vectors). **`gen.py`'s PCBC, LRW, CS3, XCBC,
  VMAC and SP 800-108 share an author with this package**: PCBC, XCBC and
  VMAC, LRW and CS3 over ciphers other than AES, and SP 800-108's feedback
  mode, are compared with them alone (no outside implementation here has
  those modes), checked first on the specifications' own vectors (and, for
  SP 800-108, against KBKDFHMAC in counter mode). The
  cases are written as several programs of 80 cases each
  (`ref/cases00.bend`, ...), run in order: one program of all of them
  outgrows a check process's memory.

## Sizes

Every loop over blocks or bytes is a tail call (the structural forms the
proofs use are proved equal to the loops), so a message has no length limit
beyond memory. Native builds (Bend 2.0.37, WSL2), each run building a 1 MB
pseudo-random message: AES-CTR through the stream interface, encryption and
decryption back, 9.6 s and 297 MB; SM4-CBC through `modes.bend`, both ways,
6.4 s and 302 MB; HMAC over CRC-32 (one call, in pieces, and verify) 0.8 s.
`check.bend` takes about 4 min with its build (PBKDF2-HMAC-SHA256 with
80,000 iterations among it); the ref test about 4 min (measured on a machine
shared with other checks).

## Notes on use

* **A CRC is not a cryptographic hash, and HMAC over one is not a secure
  MAC**: the CRC instances are checksums, and the HMAC and HKDF instances
  over them exercise those algorithms' genericity. Use SHA-256 or SHA-512
  (and HMAC and HKDF over them) for security.
* MD4, MD5, SHA-1 and Michael are here for compatibility only (see
  hashes/README.md), and HMAC-SHA-1 and PBKDF2-HMAC-SHA-1 for the protocols
  that require them.
* PBKDF2's strength is its iteration count: take it as large as the
  application allows (RFC 8018 section 4.2 asks for at least 1000).
* DES, 3DES, RC4, Blowfish, CAST-128, TEA, XTEA and FCrypt are here for
  compatibility only (see legacy-ciphers), and so are PCBC (a swap of two
  ciphertext blocks goes undetected) and LRW (IEEE 1619 replaced it with
  XTS); never reuse a CTR counter, an RC4 state, a CCM nonce or a VMAC
  nonce under one key.
* None of this code is constant-time, and Bend's runtime promises nothing
  about running time; `CrMac.verify_tag` compares every byte, which is a
  property of the code, not a timing guarantee.

## Dependencies

`DEPS`: `bytes` (Octets, and its laws in the proofs), `word64` (the bit
slicing of the 128-bit format, `W64` for CRC-64 and VMAC), `gf` (GF(2^128)
for LRW's tweaks), `cipher-modes` (AES,
CMAC, CCM and the `CmBlock` type, for the instances), `legacy-ciphers` (its
ciphers and RC4, and their laws), `crc` (its CRCs and their laws), `hashes`
(its hashes and Michael, and their laws, for the instances; only the
`inst_*` files, `check.bend` and the laws and proofs import it), and the
hub package `bend-collections-laws-crypto@1.0.0.0` (SHA-256, SHA-512 and
SHA3-256 and their laws, above; MIT). The interface and generic files
(`crypto.bend` to `hkdf.bend`, `pbkdf2.bend` and `kbkdf.bend`) import only `bytes`; only
`inst_sha2.bend`, `inst_sha3.bend` (and `PROOF.bend`) import
bend-collections-laws-crypto, and only
`inst_aes.bend` reaches bend-collections, through cipher-modes' `aes.bend`.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (about 4 min, the hashes
package's proofs included), `--verdict` ALL PROOFS CHECK (about 3 to 6 min, 2.31
GB peak), `check.bend` passes, `ref/run.sh` 499 cases match, `scripts/deps.sh`
passes.
