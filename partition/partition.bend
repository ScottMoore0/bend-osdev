# bend-osdev-partition: recognising how a disk is partitioned, from its first
# two blocks: no table, an MBR (mbr.bend), or a GPT behind its protective MBR
# (gpt.bend; UEFI Specification, chapter 5).
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./mbr.bend as M
import ./gpt.bend as G

type PartitionScheme is Data:
  PartitionNone{}
  PartitionMbr{mbr: M.Mbr}
  PartitionGpt{mbr: M.Mbr, header: G.GptHeader}
  PartitionBadGpt{mbr: M.Mbr, error: G.GptError}

def PartitionScheme.show(s: PartitionScheme) -> String:
  match s:
    case PartitionNone{}:
      "none"
    case PartitionMbr{m}:
      "mbr"
    case PartitionGpt{m, h}:
      "gpt"
    case PartitionBadGpt{m, e}:
      "bad gpt: " ++ G.GptError.show(e)

def Partition.detect.gpt(r: Result<&2, &2, G.GptError, G.GptHeader>, m: M.Mbr) -> PartitionScheme:
  match r:
    case Done{h}:
      PartitionGpt{m, h}
    case Fail{e}:
      PartitionBadGpt{m, e}

def Partition.detect.kind(protective: Bool, +m: M.Mbr, lba1: B.Octets) -> PartitionScheme:
  match protective:
    case True{}:
      Partition.detect.gpt(G.Gpt.validate_header(lba1), m)
    case False{}:
      PartitionMbr{m}

def Partition.detect.go(r: Result<&2, &2, M.MbrError, M.Mbr>, lba1: B.Octets) -> PartitionScheme:
  match r:
    case Done{+m}:
      Partition.detect.kind(M.Mbr.is_protective(m), m, lba1)
    case Fail{e}:
      PartitionNone{}

# the scheme of a disk whose first two blocks are lba0 and lba1: an MBR
# whose first record has type 0xEE is a protective MBR, and the GPT header in
# lba1 is then validated (signature, header size, header CRC)
def Partition.detect(lba0: B.Octets, lba1: B.Octets) -> PartitionScheme:
  Partition.detect.go(M.Mbr.parse(lba0), lba1)
