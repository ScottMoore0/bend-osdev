# bend-osdev

Libraries for operating-system development, written in
[Bend](https://github.com/bendlang/bend) 2: file systems, archive and
compression formats, binary formats, partition tables, network headers,
security models and the data structures a kernel uses. Each package is a
separate, replaceable component with a typed interface, laws about that
interface, proofs of those laws, and tests against an independent
implementation.

Everything here is MIT licensed and written from public specifications; no
GPL source was read.

## Status

- **Laws reviewed.** The maintainer reviews every package's laws as they
  are written. They are proved, and `--verdict` (Bend's Lean-formalised kernel) accepts them
  all except four laws in cipher-modes that its kernel cannot yet model
  (see that README).
- **Bend 2.0.37**, pinned in `BEND_VERSION`.
- **Publishing on BendHub**, every package at version 0.1.0.0, as
  `bend-osdev-<package>`: so far acpi, aead, algo, apparmor, array, bpf,
  bytes, caps, cipher-modes, crc, crypto, gf, hashes, legacy-ciphers and
  word64 (`import bend-osdev-bytes@0.1.0.0/bytes.bend as B`). The hub
  registers about five new package names a day, so the others follow over
  the coming days. File names with a `-` are published with a `_`
  (`bend-osdev-cipher-modes@0.1.0.0/cipher_modes.bend`), since the hub
  refuses `-` in a path.

## Packages

| Package | What it is |
|---|---|
| [word64](word64/) | 64-bit words: arithmetic modulo 2^64, bits, halves, text |
| [bytes](bytes/) | Byte strings (`Octets`) and fixed-width fields: the shared byte layer |
| [byte](byte/) | Typed 8- and 16-bit words (`ByteU8`, `ByteU16`) and a `U32`'s bytes, from bendlang/bend#1660, with an adapter note for packages with their own `U8` |
| [packing](packing/) | Bit fields at any bit position of a byte buffer, packed and unpacked, with lib/packing's quirks as parameters |
| [kitbytes](kitbytes/) | An adapter between `Octets` and bend-kit's `Bytes` |
| [array](array/) | Laws for Base's `Array`: get after set, other slots unchanged, size kept, agreement with a list model |
| [blockdev](blockdev/) | The block-device interfaces (pure, and owned with writes), a balanced in-memory device, and a proved `Array<U32>` image device |
| [iodev](iodev/) | Block devices in `IO`: the interface and its helpers, adapters for blockdev's devices, a disk image file read on demand, a write overlay, and a disk image read and written in place, of any size, on file effects passed in |
| [fileio](fileio/) | Library effects on Base's `File` (C and JavaScript sides): a read-write open that keeps the file, positioned writes, 64-bit reads and sizes, `fsync` |
| [crc](crc/) | CRCs in the Rocksoft parameter model (CRC-32C, CRC-32, CRC-16, CRC-T10DIF, three CRC-64s, and CRC-4, CRC-7, four CRC-8s and three CRC-16/CCITTs), bitwise and table-driven |
| [gf](gf/) | Finite fields: GF(2^8) with any polynomial (ring laws proved for every polynomial), log/exp tables, GF(2^128) in GCM, CMAC/LRW and XTS bit orders, GF(2^m) for BCH |
| [kmath](kmath/) | Integer helpers: gcd/lcm (divides-both proved), powers, integer square roots (bounds proved), 64-bit division, reciprocal division, best rational approximation, CORDIC, primes |
| [khash](khash/) | Non-cryptographic hashes: Jenkins' lookup3 (jhash, jhash2, the word forms) and golden-ratio hash_32/hash_64 |
| [rhash](rhash/) | A resizable hash table with incremental resizing (rhashtable): every key found at every step of a migration, proved for every hash and key encoding |
| [kstr](kstr/) | Text conversions: kstrtox-style strict parsing, a vsprintf number subset, hex_dump_to_buffer lines, match_token option parsing (hex round trip proved) |
| [cpio](cpio/) | cpio `newc` and `crc` archives, the initramfs format |
| [elf](elf/) | ELF32/ELF64 headers, program and section headers, symbols (with an indexed string table), relocations, the dynamic section, notes and symbol versions |
| [partition](partition/) | MBR and GPT partition tables, with GPT's CRCs |
| [uuid](uuid/) | UUIDs (RFC 9562), text and both byte orders |
| [netheaders](netheaders/) | Ethernet, ARP, IPv4, IPv6, ICMP, UDP and TCP headers, and the Internet checksum |
| [nlattr](nlattr/) | Netlink attributes (RFC 3549): building, parsing and nested attributes with both flags, and validation against policies, strict or liberal; checked against the running kernel |
| [tcpip](tcpip/) | A TCP/IP stack as a pure state machine: ARP, IPv4 with reassembly, ICMP echo, UDP, TCP (RFC 9293, 6298, 5681), tested against Linux |
| [caps](caps/) | Linux capability sets and how execve, capset and prctl change them |
| [perms](perms/) | Unix permission checks, umask, POSIX ACLs, sticky directories |
| [landlock](landlock/) | Landlock rule evaluation: rulesets, path and port rules, stacked domains, ABI 1–6, REFER rules, scoping; checked against the kernel |
| [nftables](nftables/) | nftables rule evaluation as a pure model: tables, chains, rules, sets, maps and verdict maps, counters and limits (clean-room, from documentation only) |
| [selinux](selinux/) | SELinux policy loading from CIL and evaluation: TE rules, booleans, constraints, MLS, transitions, neverallow (clean-room, from documentation only) |
| [apparmor](apparmor/) | AppArmor policy as a pure model: profile loading (includes, variables, aliases, hats, children) and access and exec decisions (clean-room, from documentation only) |
| [lz4](lz4/) | LZ4 block and frame compression and decompression |
| [xz](xz/) | `.xz` decompression: LZMA2, delta, every check type, streaming |
| [bzip2](bzip2/) | bzip2 compression and decompression, each stage (RLE, MTF, BWT, Huffman) usable alone |
| [zstd](zstd/) | Zstandard (RFC 8878) decompression with dictionaries and streaming, and a compressor; FSE, Huffman and XXH64 usable alone |
| [deflate](deflate/) | DEFLATE (RFC 1951) compression and decompression, with the zlib (RFC 1950) and gzip (RFC 1952) formats, one-shot and streaming; Huffman codes, matcher, block choice and Adler-32 usable alone |
| [lzo](lzo/) | LZO1X compression and decompression, and the lzop container (clean-room, from documentation only) |
| [c842](c842/) | IBM's 842 compression, as Linux and POWER's NX accelerator read and write it, with its CRC trailer (clean-room, from IBM's paper and patent and black-box tests of Linux) |
| [ringbuf](ringbuf/) | A kfifo-style ring buffer, with a list reference model |
| [idalloc](idalloc/) | IDR/IDA-style ID allocators |
| [errseq](errseq/) | Error sequence counters (`errseq_t`): a writer records errors, each observer learns of one it has not seen exactly once |
| [ratelimit](ratelimit/) | Rate limiting as a pure state machine: at most `burst` events per `interval` (sliding or fixed window), with the suppressed count |
| [timerqueue](timerqueue/) | Timers keyed by expiry as a pure state machine: add, delete, next expiry, expire all due; any priority queue or ordered map as the store |
| [dim](dim/) | Dynamic interrupt moderation (net_dim) as a pure state machine: profile steps from interval samples, converging on identical samples |
| [genalloc](genalloc/) | A general-purpose pool allocator in the style of genalloc, the fit algorithm a template (first, best, aligned, order-aligned, fixed offset) |
| [algo](algo/) | Bit search, bitmaps, binary search |
| [ksort](ksort/) | Sorting: a stable merge sort on lists and an in-place heapsort on an `Array`, the comparison a template |
| [textsearch](textsearch/) | Searching a byte stream that arrives in chunks, matches spanning chunk boundaries: KMP, Boyer-Moore (Horspool or good suffix) and a token automaton behind one interface |
| [xarray](xarray/) | A sparse array with marks, in the style of the kernel's XArray |
| [itree](itree/) | An augmented AVL interval tree |
| [maple](maple/) | A range-indexed B-tree in the style of the kernel's maple tree, with gap search |
| [fdt](fdt/) | Devicetree Blobs, read and written (output byte-identical to dtc's) |
| [acpi](acpi/) | ACPI tables read and written (RSDP, RSDT/XSDT, MADT, FADT, HPET, MCFG, SRAT, SLIT, BGRT), and an AML interpreter with a step bound |
| [fat](fat/) | FAT12/16/32, read and write: format, create, write, truncate, delete, rename |
| [iso9660](iso9660/) | ISO 9660 with Rock Ridge, Joliet and El Torito, read-only |
| [ext2](ext2/) | ext2, ext3 and ext4 (extents, checksums), read and write: mkfs, files, directories, links, rename, write and truncate, fsck |
| [ext4](ext4/) | ext4 beyond ext2: hashed directories (htree, with a writer), the jbd2 journal (recovery, commits, transactions), inline data and extended attributes |
| [cipher-modes](cipher-modes/) | CBC, PKCS #7, XTS, CCM and CMAC over any block cipher, AES by default |
| [legacy-ciphers](legacy-ciphers/) | DES, 3DES, SM4, Camellia, Serpent, Twofish, ARIA, CAST-256, Blowfish, CAST-128, TEA, XTEA, FCrypt and RC4 (for compatibility); the 128-bit ciphers plug into cipher-modes, with 64-bit ECB/CBC |
| [hashes](hashes/) | MD4, MD5, SHA-1, RIPEMD-160, SM3, Streebog-256/512 and Michael (TKIP's MIC), streaming and one-shot, through one Merkle–Damgård engine (streaming, split and digest length proved for every input) |
| [siphash](siphash/) | SipHash-c-d (64- and 128-bit output) and HalfSipHash-c-d (32- and 64-bit) for any number of rounds, streaming and one-shot, with Linux's SipHash-2-4, SipHash-1-3 and HalfSipHash-1-3 named; streaming, split and output length proved for every input; all 256 published vectors, checked against openssl |
| [crypto](crypto/) | The crypto interfaces (block and stream cipher, hash, MAC, AEAD, KDF, signature, key agreement) with their laws; HMAC, HKDF, PBKDF2 and the SP 800-108 KDFs (counter and feedback), ECB, CBC, CTR, PCBC, CBC-CS3 ciphertext stealing, LRW, XCBC-MAC and VMAC over any instance; the existing ciphers, MACs, AEADs and CRCs, the hashes package's hashes and Michael, and SHA-256, SHA-512 and SHA3-256 (from bend-collections), as instances |
| [aead](aead/) | AEGIS-128, encrypt-then-MAC over any cipher and MAC (the kernel's authenc), and the IV generators ESSIV, seqiv and echainiv over any AEAD, as instances of crypto's AEAD interface |
| [bignum](bignum/) | Natural numbers of any size for public-key cryptography: bytes (OS2IP/I2OSP), arithmetic, Montgomery multiplication, modular exponentiation and inverse, Miller-Rabin, the Jacobi symbol |
| [rsa](rsa/) | RSA (RFC 8017): the primitives with the CRT, RSASSA-PKCS1-v1_5 and RSASSA-PSS, RSAES-OAEP and RSAES-PKCS1-v1_5, MGF1 over any hash, key generation, a raw key form (encoding round trips proved) |
| [dh](dh/) | Finite-field Diffie-Hellman (SP 800-56A): key pairs, full, partial and Legendre-symbol validation, the primitive; RFC 7919's ffdhe and RFC 3526's MODP groups, computed from their formulas |
| [ecc](ecc/) | Elliptic curves over prime fields, generic over the domain parameters: Jacobian arithmetic, validation (soundness proved), SEC 1 points; NIST P-192 to P-521, SM2's and the GOST CryptoPro curves; ECDH, and ECDSA with RFC 6979's deterministic k |
| [sm2](sm2/) | SM2 digital signatures (draft-shen-sm2-ecdsa-02): Z_A, signing and verification over any curve and hash, SM3 by default |
| [ecrdsa](ecrdsa/) | GOST R 34.10-2012 signatures (RFC 7091) over any curve and hash, Streebog by default, with RFC 4491's key and signature forms |
| [pubkey](pubkey/) | RSA, DH, ECDSA, ECDH, SM2 and GOST R 34.10-2012 as instances of crypto's signature and key-agreement interfaces, generic over hash, curve and group, with the interfaces' laws for each |
| [kithash](kithash/) | An adapter for bend-kit-hash: its CRC-32, Adler-32, FNV-1a, XXH32 and XXH64 as instances of crypto's hash interface, and its SipHash-1-3 with siphash's SipHash and HalfSipHash as MAC instances, on `Octets`; agreement with crc, deflate, zstd and siphash proved on vectors and tested on random inputs; an audit of bend-kit-hash (AUDIT.md) |
| [jitter](jitter/) | The core of a CPU Jitter RNG (jitterentropy) on given time deltas: the stuck test, SP 800-90B's RCT and APT, and the conditioner as a parameter: SHA3-256 through crypto's hash interface (the default), or jitterentropy 3.7.0's XDRBG over SHAKE256 |
| [jitterclock](jitterclock/) | A monotonic nanosecond clock as a library effect (C and JavaScript sides), timing a hash loop to feed jitter |
| [bpf](bpf/) | Classic BPF and seccomp filters, checked against the running kernel |
| [ebpf](ebpf/) | An eBPF interpreter (RFC 9669) with a bounds-checked memory model, and a verifier |
| [xorblocks](xorblocks/) | XOR of byte blocks (xor_blocks): two blocks under a length policy, many into one, laws of XOR proved |
| [raid6](raid6/) | RAID-6 P and Q syndromes and the recovery of any one or two lost blocks (Anvin's paper), recovery proved for every stripe |
| [rs](rs/) | Reed-Solomon codes over GF(2^m) with every parameter open: systematic encoding, decoding of errors and erasures (Berlekamp-Massey, Chien, Forney) |
| [bch](bch/) | Binary BCH codes: encoding, Berlekamp-Massey and Chien decoding on bits and on NAND sectors with their ECC bytes |
| [asn1](asn1/) | ASN.1 BER and DER (X.690): decoding with every DER rule a parameter, encoding, typed values, and schemas as Bend values; decode after encode, DER's uniqueness and reading within the buffer proved for every input; checked against openssl asn1parse |
| [oid](oid/) | Object identifiers: DER through asn1, dotted text (X.680 32.3) with leading zeros a parameter, and a registry of 127 names from RFC 5280, PKCS #1, the ECC and CMS RFCs and NIST CSOR; DER and text round trips and DER canonicity proved for every input; checked against OpenSSL and Python cryptography |
| [x509](x509/) | X.509 v3 certificates (RFC 5280): every field read with the signed tbsCertificate octets kept, each profile check a rule, names compared per RFC 5280 7.1 or binary, and signature checking through crypto's interface; parsed certificates conform and the signature check covers exactly the signed octets, proved for every input; checked against Python cryptography and OpenSSL |
| [pkcs](pkcs/) | CMS SignedData (RFC 5652, PKCS #7) with each signer's exact signed octets and signature checking through crypto's interface, and PKCS #8 private keys (RFC 5208, 5958, 8410); parsed messages and keys conform and the signature check covers exactly the signed octets, proved for every input; checked against OpenSSL and Python cryptography |

Each package's README lists its files, public interface, extension points,
laws, tests, limits and status.

## Layout of a package

```
pkg/
  pkg.bend      the entry file (one file per concern beside it)
  LAWS.bend     laws about the public interface
  PROOF.bend    their proofs
  check.bend    examples, with their expected output in #| lines
  ref/          the differential test against an independent implementation
  gen/          generators for any generated proof or law files
  DEPS          the packages it imports
  README.md, VERSION, LICENSE
```

[CONVENTIONS.md](CONVENTIONS.md) gives the rules that keep packages
separable and changeable, [REVIEW.md](REVIEW.md) the checklist each package
passes before it is committed, and [AGENTS.md](AGENTS.md) how to build one,
with Bend's pitfalls and limits.

## Checking

```bash
scripts/install-bend.sh "$HOME/.bend"
scripts/deps.sh
scripts/check.sh
```

`scripts/check.sh [package...]` checks the proofs, runs `check.bend` and the
reference test of each package (all of them by default). `VERDICT=1` also
rechecks the proofs with `--verdict`, which needs Lean 4.34.0. Programs run as
native binaries, which needs clang 14 or newer (`$CC` or on PATH); the
reference tests need python3 and the tools listed in
`.github/workflows/check.yml` (each skips, with exit 77, when its tool is
missing).

## Publishing

`scripts/publish.py --check [package...]` stages each package as it would be
published (its sibling imports rewritten as hub imports) and checks it;
`scripts/publish.py [package...]` publishes it on BendHub as
`bend-osdev-<package>@<VERSION>`, dependencies first, after `bend login`.

## Licence

MIT; see [LICENSE](LICENSE).

Written with Claude Code (Claude Opus 5.5).
