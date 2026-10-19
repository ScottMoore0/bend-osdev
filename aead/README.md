# bend-osdev-aead

Authenticated encryption with associated data, as instances of
bend-osdev-crypto's AEAD interface (`crypto/aead.bend`, the shape of RFC
5116): AEGIS-128; encrypt-then-MAC over any cipher with an IV and any MAC
(the Linux kernel's `authenc`); and the IV generators ESSIV, seqiv and
echainiv, which make one AEAD (or, for ESSIV, one cipher with an IV) into
another. The generic constructions take the crypto package's interfaces as
template arguments, so they run over every block cipher, hash, MAC and AEAD
that plugs into them.

The directory is `aead` and the entry file `aead/aead.bend`; the hub name is
`bend-osdev-aead`.

## Specifications

Written from the public specifications only:

* **AEGIS-128:** H. Wu, B. Preneel, *AEGIS: A Fast Authenticated Encryption
  Algorithm (v1.1)*, CAESAR competition final portfolio (2016), section 2.3
  (AEGIS-128, the 128-bit key and nonce variant). RFC 9312 is *not* AEGIS
  (it is about QUIC manageability); the IETF's AEGIS document, RFC 10032,
  specifies AEGIS-128L and AEGIS-256 but not AEGIS-128, and is used here
  only for its AESRound test vector (Appendix A.1).
* **The AES round function:** FIPS 197, *Advanced Encryption Standard*
  (2001), sections 5.1.1 to 5.1.4 (SubBytes, ShiftRows, MixColumns,
  AddRoundKey).
* **Encrypt-then-MAC:** D. McGrew, J. Foley, K. Paterson, *Authenticated
  Encryption with AES-CBC and HMAC-SHA* (draft-mcgrew-aead-aes-cbc-hmac-sha2-05,
  2014), section 2.1; RFC 7518, *JSON Web Algorithms*, section 5.2 (the same
  construction) and its Appendix B.1 test vector; the Linux kernel's
  `authenc` layout (MAC over A || C), as observed through AF_ALG, and its
  values (below).
* **ESSIV:** C. Fruhwirth, *New Methods in Hard Disk Encryption* (2005),
  section 4.2 (IV = E(H(K), sector)).
* **seqiv, echainiv:** the IV constructions of RFC 8446, section 5.3 (a
  sequence number XORed into a secret salt), RFC 5116, section 3.2 (nonces
  from a counter), and NIST SP 800-38A, Appendix C (an IV for CBC as the
  encryption of a nonce); the IV travels in front of the ciphertext, as
  ESP's explicit IV does (RFC 4303).
* **CBC and PKCS #7 padding:** through bend-osdev-crypto's `modes.bend` (SP
  800-38A) and cipher-modes' `pkcs7.bend` (RFC 5652, section 6.3).

No GPL source was read: the kernel served only as a black box through
AF_ALG, in the differential test.

## Files

| File | Holds |
|---|---|
| `aead.bend` | the entry file: a ciphertext with its tag appended, and split again (`AdTag`) |
| `aesround.bend` | the AES round function AESRound on 16-byte blocks (`AdBlk`), its S-box table generated |
| `aegis128.bend` | AEGIS-128 as an AEAD |
| `authenc.bend` | encrypt-then-MAC over any cipher with an IV and any MAC, with two named MAC inputs |
| `ivcipher.bend` | any block cipher in CBC, with or without PKCS #7 padding, as a cipher with an IV (for `authenc.bend` and `essiv.bend`) |
| `essiv.bend` | ESSIV over a cipher with an IV or over an AEAD |
| `seqiv.bend` | seqiv over any AEAD |
| `echainiv.bend` | echainiv over any AEAD |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `check.bend` | the specifications' vectors and outside values, with expected output |
| `gen/tables.py` | writes the AES S-box region of `aesround.bend` from FIPS 197's definition (`--check` checks it) |
| `gen/proof.py` | writes the lemmas proved on a word's 32 bits (the "bits" region of `PROOF.bend`) |
| `ref/gen.py`, `ref/run.sh`, `ref/model.py` | the differential test, and the AEGIS-128 model it uses |

Bend imports do not re-export: import the files you use.

## Public interface

| File | Defs and types |
|---|---|
| `aead.bend` | `AdSplit{c, t}` (open), `AdTag.split(tlen, o)` (`CrTooShort` for fewer than tlen bytes), `AdTag.join(c, t)`, `AdTag.is_eq(a, b)` |
| `aesround.bend` | `AdBlk{w0, w1, w2, w3}` (open: four big-endian words, one AES column each), `AdBlk.zero`, `.xor`, `.and`, `.of_list`, `.to_list`, `.of_octets`, `.to_octets`, `.hex`; `AdSbox` (opaque), `AdAes.sbox()`, `AdAes.round(s, a, k)` |
| `aegis128.bend` | `AdAegisKey` (opaque), `AdAegis128.key` (16 bytes, `CrBadKeyLength`), `AdAegis128.seal(k, nonce, aad, p)` (a 16-byte nonce, `CrBadNonceLength`; C followed by the 16-byte tag), `AdAegis128.open` (`CrTooShort`, `CrTagMismatch`), `AdAegis128.tag_of(k, nonce, aad, c)` |
| `authenc.bend` | `AdAuthencKey<KE, KM>{ke, km}`, `AdAuthenc.key(~KE, ~KM, ~ekey, ~mkey, ~elen, o)` (the MAC key, then the elen-byte cipher key), `AdAuthenc.key_of`; `AdAuthenc.input_kernel` (A || C), `AdAuthenc.input_mcgrew` (A || IV || C || AL); `AdAuthenc.tag`, `AdAuthenc.seal(~KE, ~KM, ~enc, ~mac, ~input, ~tlen, k, iv, aad, p)` (C || T), `AdAuthenc.open(.., ~dec, ..)` (the tag checked before anything is decrypted) |
| `ivcipher.bend` | `AdCbc.encrypt`, `AdCbc.decrypt` (whole blocks), `AdCbc.encrypt_padded`, `AdCbc.decrypt_padded` (PKCS #7), each over a block cipher's template arguments |
| `essiv.bend` | `AdEssivKey<KD, KS>{kd, ks}`, `AdEssiv.key(~KD, ~KS, ~dkey, ~skey, ~digest, o)` (the data key, and the salt cipher's key H(K)), `AdEssiv.iv`, `AdEssiv.encrypt`, `AdEssiv.decrypt` (over a cipher with an IV), `AdEssiv.seal`, `AdEssiv.open` (over an AEAD) |
| `seqiv.bend` | `AdSeqivKey<KA>{ka, salt}`, `AdSeqiv.key(~KA, ~akey, ~ivlen, o)` (the AEAD's key, then an ivlen-byte salt), `AdSeqiv.iv(k, seq)`, `AdSeqiv.seal(~KA, ~seal, k, seq, aad, p)` (IV || C), `AdSeqiv.open(~KA, ~open, ~ivlen, k, seq, aad, c)` |
| `echainiv.bend` | `AdEchainivKey<KA, KC>{ka, kc, salt}`, `AdEchainiv.key(~KA, ~KC, ~akey, ~ckey, ao, co, salt)`, `AdEchainiv.iv`, `AdEchainiv.seal`, `AdEchainiv.open` |

Errors are bend-osdev-crypto's `CrError`. Everything else (`ad.*`, the
AEGIS state types) is internal.

As AEADs of the crypto interface (`~K`, `~key`, `~seal`, `~open`):
AEGIS-128 is `~AdAegisKey, ~AdAegis128.key, ~AdAegis128.seal,
~AdAegis128.open`; encrypt-then-MAC, ESSIV over an AEAD, seqiv and echainiv
are AEADs once their template arguments are given (the IV in the place of
the nonce, the sequence number for seqiv and echainiv).

## How the constructions are put together

* **AEGIS-128** keeps the AES S-box in its key (`AdAegisKey{k, sb}`), so
  the table is built once per key. The message is processed a byte at a
  time: each byte meets the next keystream byte and joins the block that
  updates the state when it is whole, so decryption runs through the same
  states as encryption, which is what the round-trip proof follows.
* **Encrypt-then-MAC**: C = Enc(K_E, IV, P), T = the first tlen bytes of
  MAC(K_M, input(A, IV, C)), the output C || T; open compares the whole tag
  (`AdTag.is_eq`, every byte) before decrypting. `input_kernel` is the
  kernel's `authenc` (an IV to be authenticated is part of A, as ESP puts
  it); `input_mcgrew` is the McGrew draft's and RFC 7518's (with PKCS #7
  padding and the IV sent apart). A MAC shorter than tlen is zero-padded.
* **ESSIV**: IV' = E(H(K), IV) under the salt cipher, then the wrapped
  cipher or AEAD under K and IV'; dm-crypt's aes-cbc-essiv:sha256 is AES-CBC
  with SHA-256 and AES-256 as the salt cipher.
* **seqiv**: IV = salt XOR the sequence number (right-aligned), sealed as
  IV || AEAD.seal(K, IV, A || IV, P). **echainiv**: IV = E(Kc, salt XOR the
  sequence number), likewise. The IV is part of the wrapped AEAD's
  associated data, so a changed IV is refused even under an AEAD that does
  not bind its nonce (encrypt-then-MAC over A || C: without that, CBC would
  let a changed IV through, garbling only the first block, which is what
  this package's differential test found in an earlier draft). The kernel's
  seqiv and echainiv draw their salts at random, so their IVs differ from
  these; a receiver reads the IV from the packet in both.

## Streaming

None of the constructions streams: they are AEADs of crypto's interface,
which takes whole messages, and an AEAD's open must not release any
plaintext before the tag over the whole ciphertext is checked
(encrypt-then-MAC checks it before decrypting; AEGIS-128 decrypts, then
checks, and returns the plaintext only when the tag matches). A message arriving in
pieces is gathered first; AEGIS-128's state runs over it a byte at a time
internally, so a streaming seal could be added over the same state without
changing the laws' statements.

## Extension points

* **Any cipher, MAC, hash or AEAD** of bend-osdev-crypto's interfaces plugs
  into the generic constructions: `authenc.bend` takes `~enc`/`~dec` (a key
  schedule, an IV and bytes) and a MAC (`~KM`, `~mkey`, `~mac`), so
  authenc(cmac(aes), cbc(sm4)) is as available as
  authenc(hmac(sha256), cbc(aes)); `essiv.bend` takes any hash (`~digest`)
  and any block cipher as the salt cipher; `seqiv.bend` and `echainiv.bend`
  any AEAD (and echainiv any block cipher for the IV).
* **Named defaults that can be replaced**: the MAC input (`input_kernel`,
  `input_mcgrew`, or any `~input: A -> IV -> C -> bytes`), the tag length
  (`~tlen`), the IV length (`~ivlen`), padding or not (`ivcipher.bend`).
* **AESRound** (`aesround.bend`) is public, so the other members of the
  AEGIS family (AEGIS-128L, AEGIS-256) can be built on it.

## Laws

`LAWS.bend` has 9 laws, all proved (`PROOF.bend`), and all accepted by
`--verdict`.

* **AEGIS-128, for every key, nonce, associated data and message:**
  `aegis128_round_trip` (crypto's AEAD round trip: open accepts what seal
  produced and gives the message back, and when seal refuses, so does
  open-after-seal); `aegis128_tamper` (under a 16-byte nonce, a 16-byte tag
  other than `AdAegis128.tag_of`'s for the ciphertext is refused with
  `CrTagMismatch`).
* **Encrypt-then-MAC, over every cipher and MAC:** `authenc_round_trip_if`
  (the round trip, wherever the cipher's decryption undoes its encryption at
  that key, IV and message: hypothesis `h`, used once, as crypto's README
  explains); `authenc_tamper` (a tlen-byte tag other than the computed one
  is refused, for every key, IV, associated data and ciphertext).
* **ESSIV:** `essiv_round_trip_if` (over a cipher with an IV) and
  `essiv_aead_round_trip_if` (over an AEAD): the round trip wherever the
  wrapped algorithm's holds at the derived IV.
* **seqiv, echainiv:** `seqiv_round_trip_if`, `echainiv_round_trip_if`: the
  round trip wherever the wrapped AEAD's holds at the generated IV and
  associated data A || IV, given that the IV has the nonce's length (`hl`).
* **Vector:** `aesround_rfc10032` (RFC 10032, Appendix A.1).

**Not proved, and tested:** a changed ciphertext or associated data
refused (a forgery succeeds with probability about 2^-8tlen, so it is no
law for every input; tested for every construction in `check.bend` and
`ref/`); AEGIS-128's values (no AEGIS-128 vector is published in the
specification; compared with `ref/model.py`, which shares the author); the
round trips of the generic constructions unconditionally (they hold where
the wrapped algorithm's do: for a crypto instance with a proved round trip
the hypothesis is that law at the arguments used).

## Tests

* `check.bend`: RFC 10032's AESRound vector; AEGIS-128 sealed and opened
  back for five inputs (the empty message, a whole block, two blocks with
  associated data, a 13-byte message, a 61-byte message after 32 bytes of
  associated data), a changed tag, a 15-byte key, a 15-byte nonce and a
  ciphertext shorter than a tag refused (values from `ref/model.py`);
  encrypt-then-MAC on RFC 7518's Appendix B.1 (AES_128_CBC_HMAC_SHA_256),
  sealed and opened, with its tag changed refused; encrypt-then-MAC in the
  kernel's layout (the kernel's authenc(hmac(sha256), cbc(aes)) value);
  ESSIV over AES-CBC with SHA-256, both ways (the kernel's
  essiv(cbc(aes), sha256) values); seqiv over AES-CCM, sealed and opened,
  with a changed IV byte and a short message refused (cryptography's
  AESCCM); echainiv over authenc(hmac(sha256), cbc(aes)), sealed and
  opened, with a changed IV byte refused (the kernel's authenc and
  cryptography's AES). The script that computed the values first checked
  the kernel's against cryptography's AES and Python's hmac.
* `ref/run.sh` (46 cases with the default seed): encrypt-then-MAC in the
  kernel's layout against the kernel's authenc(hmac(sha256), cbc(aes))
  through AF_ALG (MAC keys of 0 to 100 bytes, AES-128 and AES-256, 16- and
  32-byte tags, a changed tag refused); in the McGrew layout against
  cryptography's AES-CBC and PKCS #7 padding and Python's hmac (that layout
  first checked on RFC 7518 B.1); ESSIV against the kernel's
  essiv(cbc(aes), sha256), both ways; seqiv over AES-CCM against
  cryptography's AESCCM; echainiv over the kernel's authenc; AEGIS-128
  against `ref/model.py`, with a changed tag and a changed ciphertext byte
  refused. Without AF_ALG the kernel cases fall back to cryptography and
  hmac, which `gen.py` checks against the kernel when it is there. **The
  AEGIS-128 model (`ref/model.py`) shares an author with this package**: it
  was written from the same specification, and its agreement is a second
  reading of that specification, not an independent implementation's (its
  AES round is checked against RFC 10032's vector).

## Sizes

Every loop is a tail call, so a message has no length limit beyond memory.
Native builds (Bend 2.0.37, WSL2), including the build: AEGIS-128 sealing
and opening 64 KB, 3.2 s and 330 MB; encrypt-then-MAC with HMAC-SHA-256 and
AES-CBC over 64 KB both ways, 17 s and 620 MB. `check.bend` takes about
23 s with its build.

## Notes on use

* Never reuse a nonce under one AEGIS-128 key, or a sequence number under
  one seqiv or echainiv key. ESSIV gives an unpredictable IV per sector; it
  is no AEAD over a cipher with an IV.
* None of this code is constant-time; `AdTag.is_eq` compares every byte,
  which is a property of the code, not a timing guarantee.

## Dependencies

`DEPS`: `bytes` (Octets, and its laws in the proofs), `word64` (the 64-bit
lengths of AEGIS and the McGrew input), `cipher-modes` (PKCS #7 padding; AES
and its block type for `check.bend`), `crypto` (the interfaces, `CrError`, CBC,
`octets.bend`; the AES, CCM, SHA-256 and HMAC instances for `check.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (about 2 s), `--verdict` ALL
PROOFS CHECK (about 4 s), `check.bend` passes, `ref/run.sh` 46 cases match,
`scripts/deps.sh` passes.
