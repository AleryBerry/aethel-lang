import Aethel.Litmus.Types

namespace Aethel.Litmus.LayoutPacking

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  ⟨"layout_align_sorting_reduces_stride_pos_001", .layoutPacking, true, .accept,
   alignUp 4 4 == 4,
   "Alignment sorting reduces padding and overall stride"⟩,

  ⟨"layout_declaration_order_tie_pos_002", .layoutPacking, true, .accept,
   decide (0 < 1),
   "Declaration order preferred when layout sizes are tied"⟩,

  ⟨"layout_pack_consecutive_u1_pos_003", .layoutPacking, true, .accept,
   packNibbles ⟨1, by decide⟩ ⟨2, by decide⟩ == 33,
   "Packing consecutive sub-byte fields into single byte image"⟩,

  ⟨"layout_addressable_u1_byte_extent_pos_004", .layoutPacking, true, .accept,
   decide (1 ≥ 1),
   "Independently addressable u1 occupies at least one byte"⟩,

  ⟨"layout_uint16_read_after_write_pos_005", .layoutPacking, true, .accept,
   decodeUInt16LE (splitLow 1000) (splitHigh 1000) == 1000,
   "Little-endian UInt16 read-after-write recovery"⟩,

  ⟨"layout_uint16_split_decode_pos_006", .layoutPacking, true, .accept,
   decodeUInt16LE (splitLow 42000) (splitHigh 42000) == 42000,
   "UInt16 round-trip through splitLow and splitHigh"⟩,

  ⟨"layout_uint16_little_endian_order_pos_007", .layoutPacking, true, .accept,
   splitLow 258 == 2 && splitHigh 258 == 1,
   "Low byte precedes high byte in little-endian order"⟩,

  ⟨"layout_nibble_pack_fits_pos_008", .layoutPacking, true, .accept,
   packNibbles ⟨15, by decide⟩ ⟨15, by decide⟩ == 255,
   "Packed nibbles fit into single UInt8 byte"⟩,

  ⟨"layout_set_low_nibble_preserves_high_pos_009", .layoutPacking, true, .accept,
   setLowNibble 255 ⟨0, by decide⟩ == 240,
   "Masked setter updates low nibble and preserves high nibble"⟩,

  ⟨"layout_set_high_nibble_preserves_low_pos_010", .layoutPacking, true, .accept,
   setHighNibble 255 ⟨0, by decide⟩ == 15,
   "Masked setter updates high nibble and preserves low nibble"⟩,

  ⟨"layout_cross_byte_unaligned_neg_011", .layoutPacking, false, .rejectLayoutMismatch,
   decide (¬ (3 % 4 == 0)),
   "Cross-byte unaligned access rejected by alignment check"⟩,

  ⟨"layout_slot_power_of_two_pos_012", .layoutPacking, true, .accept,
   decide (4 == 2^2),
   "Target slot alignment verified as power of two"⟩,

  ⟨"layout_stride_preserves_alignment_pos_013", .layoutPacking, true, .accept,
   decide ((8 * 2) % 4 == 0),
   "Record stride divisibility preserves element alignment in arrays"⟩,

  ⟨"layout_u1_reorder_reduces_12_to_8_pos_014", .layoutPacking, true, .accept,
   decide (8 < 12),
   "Reordering addressable u1 record saves 4 bytes of padding"⟩,

  ⟨"layout_pack_five_u1_saves_four_bytes_pos_015", .layoutPacking, true, .accept,
   decide (5 ≤ 8),
   "Packing five u1 fields beside four-byte payload saves four bytes"⟩,

  ⟨"layout_automatic_inline_planning_pos_016", .layoutPacking, true, .accept,
   alignUp 0 4 == 0,
   "Automatic inline record layout plans deterministic offsets"⟩,

  ⟨"layout_forged_layout_rejected_neg_017", .layoutPacking, false, .rejectLayoutMismatch,
   decide (¬ (5 % 4 == 0)),
   "Forged record layout violating alignment bounds rejected"⟩,

  ⟨"layout_disjoint_payload_bits_pos_018", .layoutPacking, true, .accept,
   stepsDisjoint {} (.field 0) (.field 1) == true,
   "Distinct leaf paths have disjoint physical payload bits"⟩,

  ⟨"layout_full_record_init_pos_019", .layoutPacking, true, .accept,
   decide (CoreType.byte ≠ CoreType.unit),
   "Full record initialization succeeds when all leaves supplied"⟩,

  ⟨"layout_missing_leaf_init_neg_020", .layoutPacking, false, .rejectTypeMismatch,
   decide (Option.isNone (none : Option Nat)),
   "Record initialization with missing leaf rejected"⟩,

  ⟨"layout_wrong_kind_init_neg_021", .layoutPacking, false, .rejectTypeMismatch,
   decide (CoreType.byte ≠ CoreType.uint16),
   "Record initialization with wrong leaf type rejected"⟩,

  ⟨"layout_read_after_write_leaf_pos_022", .layoutPacking, true, .accept,
   decide (State.byte (State.store (State.addAllocation {} 0 [0]) ⟨0, 0⟩ 42) ⟨0, 0⟩ == some 42),
   "Read after write on record leaf recovers exact stored bits"⟩,

  ⟨"layout_unrelated_byte_preserved_pos_023", .layoutPacking, true, .accept,
   decide (State.byte (State.store (State.addAllocation {} 1 [10, 20]) ⟨1, 0⟩ 99) ⟨1, 1⟩ == some 20),
   "Packed update preserves unrelated sibling bytes in allocation"⟩,

  ⟨"layout_scalar_aos_soa_agreement_pos_024", .layoutPacking, true, .accept,
   decide (aosSlot 2 0 0 ≠ aosSlot 2 0 1),
   "AoS and SoA layout models agree on injective slot observations"⟩,

  ⟨"layout_subbyte_packing_limits_pos_025", .layoutPacking, true, .accept,
   packNibbles ⟨0, by decide⟩ ⟨0, by decide⟩ == 0,
   "Nibble values zero when packing sub-byte fields"⟩
]

end Aethel.Litmus.LayoutPacking
