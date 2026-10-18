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

- **Draft.** Every package's `LAWS.bend` still opens with `# DRAFT: not yet
  reviewed by the maintainer`. The laws are proved, and `--verdict` (Bend's
  Lean-formalised kernel) accepts them all except four laws in cipher-modes
  that its kernel cannot yet model (see that README), but the choice of laws
  has not been reviewed.
- **Bend 2.0.37**, pinned in `BEND_VERSION`.
- **Not yet published** on the Bend hub; every package is at version
  0.1.0.0.

## Packages

| Package | What it is |
|---|---|
| [word64](word64/) | 64-bit words: arithmetic modulo 2^64, bits, halves, text |
| [bytes](bytes/) | Byte strings (`Octets`) and fixed-width fields: the shared byte layer |
| [kitbytes](kitbytes/) | An adapter between `Octets` and bend-kit's `Bytes` |
| [array](array/) | Laws for Base's `Array`: get after set, other slots unchanged, size kept, agreement with a list model |
| [blockdev](blockdev/) | The block-device interfaces (pure, and owned with writes), a balanced in-memory device, and a proved `Array<U32>` image device |
| [crc](crc/) | CRCs in the Rocksoft parameter model (CRC-32C, CRC-32, CRC-16, CRC-T10DIF, three CRC-64s), bitwise and table-driven |
| [cpio](cpio/) | cpio `newc` and `crc` archives, the initramfs format |
| [elf](elf/) | ELF32/ELF64 headers, program and section headers, symbols (with an indexed string table), relocations, the dynamic section, notes and symbol versions |
| [partition](partition/) | MBR and GPT partition tables, with GPT's CRCs |
| [uuid](uuid/) | UUIDs (RFC 9562), text and both byte orders |
| [netheaders](netheaders/) | Ethernet, ARP, IPv4, IPv6, ICMP, UDP and TCP headers, and the Internet checksum |
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
| [lzo](lzo/) | LZO1X compression and decompression, and the lzop container (clean-room, from documentation only) |
| [ringbuf](ringbuf/) | A kfifo-style ring buffer, with a list reference model |
| [idalloc](idalloc/) | IDR/IDA-style ID allocators |
| [algo](algo/) | Bit search, bitmaps, binary search |
| [xarray](xarray/) | A sparse array with marks, in the style of the kernel's XArray |
| [itree](itree/) | An augmented AVL interval tree |
| [maple](maple/) | A range-indexed B-tree in the style of the kernel's maple tree, with gap search |
| [fdt](fdt/) | Devicetree Blobs, read and written (output byte-identical to dtc's) |
| [acpi](acpi/) | ACPI tables read and written (RSDP, RSDT/XSDT, MADT, FADT, HPET, MCFG, SRAT, SLIT, BGRT), and an AML interpreter with a step bound |
| [fat](fat/) | FAT12/16/32, read-only |
| [iso9660](iso9660/) | ISO 9660 with Rock Ridge, Joliet and El Torito, read-only |
| [ext2](ext2/) | ext2, ext3 and ext4 (extents, checksums), read-only |
| [cipher-modes](cipher-modes/) | CBC, PKCS #7, XTS, CCM and CMAC over any block cipher, AES by default |
| [legacy-ciphers](legacy-ciphers/) | DES, 3DES, SM4, Camellia, Serpent, Twofish and RC4 (for compatibility); the 128-bit ciphers plug into cipher-modes, with 64-bit ECB/CBC |
| [bpf](bpf/) | Classic BPF and seccomp filters, checked against the running kernel |
| [ebpf](ebpf/) | An eBPF interpreter (RFC 9669) with a bounds-checked memory model, and a verifier |

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

## Licence

MIT; see [LICENSE](LICENSE).

Written with Claude Code (Claude Opus 5.5).
