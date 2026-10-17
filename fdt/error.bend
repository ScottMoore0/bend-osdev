# bend-osdev-fdt, error.bend: why a devicetree blob, or a property value, was
# refused. One constructor per failure, so a caller can tell them apart.
import Base

type FdtError is Data:
  # the blob is shorter than the 40-byte header
  FdtTooShort{}
  # the first four bytes are not 0xd00dfeed
  FdtBadMagic{}
  # a version the options do not accept
  FdtBadVersion{}
  # last_comp_version above 17 (newer than this reader) or above version
  FdtBadLastComp{}
  # totalsize below the header's 40 bytes, or past the end of the blob
  FdtBadTotalSize{}
  # off_mem_rsvmap not 8-aligned, inside the header, or past totalsize
  FdtBadRsvmap{}
  # off_dt_struct not 4-aligned, inside the header, or the block past totalsize
  FdtBadStruct{}
  # the strings block inside the header, or past totalsize
  FdtBadStrings{}
  # the reservation block reaches totalsize without its terminating 0, 0 entry
  FdtRsvUnterminated{}
  # a token other than FDT_BEGIN_NODE, FDT_END_NODE, FDT_PROP, FDT_NOP, FDT_END
  FdtBadToken{tag: U32}
  # the structure block ends inside a token, or before FDT_END
  FdtTruncated{}
  # bytes after FDT_END inside the structure block (version 17 blobs)
  FdtAfterEnd{}
  # an FDT_END_NODE with no node open, FDT_END with nodes open, a second root
  # node, or a property outside every node
  FdtUnbalanced{}
  # FDT_END before any node
  FdtNoRoot{}
  # a property after a child node, when the options require properties first
  FdtPropAfterNode{}
  # an FDT_NOP, when the options refuse them
  FdtNopRefused{}
  # a property's nameoff outside the strings block, or no NUL after it
  FdtBadNameOff{}
  # a property value of the wrong length for its type
  FdtBadLength{}
  # a string value without its NUL, or with a NUL inside it
  FdtBadString{}
  # #address-cells or #size-cells above 2 (wider than 64 bits), or both 0
  FdtBadCells{}
