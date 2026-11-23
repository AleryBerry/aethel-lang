import Aethel.IntegerLayout

namespace Aethel.FlagRecordLayout

/-- A consecutive group of u1 fields followed by a four-byte payload.
The bit vector represents the logical flags, irrespective of their storage. -/
structure Value (flags : Nat) where
  bits : BitVec flags
  payload : Fin 4 → UInt8

def unpacked (flags : Nat) : RecordLayout :=
  let payloadOffset := alignUp flags 4
  ⟨payloadOffset + 4, 4, List.ofFn (fun i : Fin flags => ⟨i.val, 1, 1⟩) ++ [⟨payloadOffset, 4, 4⟩]⟩

/-- The flags share the byte at offset four. The payload moves to offset
zero and trailing padding preserves alignment in arrays of records. -/
def packed : RecordLayout :=
  ⟨8, 4, [⟨0, 4, 4⟩, ⟨4, 1, 1⟩]⟩

theorem packed_valid : packed.Valid := by decide

theorem packed_bit_fits (fits : flags ≤ 8) (i : Fin flags) :
    (IntegerType.unsigned .w1).checkPackedByte i.val = true := by
  rw [IntegerType.checkPackedByte_correct]
  change 1 < 8 ∧ i.val + 1 ≤ 8
  exact ⟨by decide, Nat.le_trans i.isLt fits⟩

theorem unpacked_valid {flags : Nat} (positive : 0 < flags) (fits : flags ≤ 8) :
    (unpacked flags).Valid := by
  have widths : flags = 1 ∨ flags = 2 ∨ flags = 3 ∨ flags = 4 ∨ flags = 5 ∨
      flags = 6 ∨ flags = 7 ∨ flags = 8 := by omega
  rcases widths with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem packed_no_larger {flags : Nat} (positive : 0 < flags) :
    packed.size ≤ (unpacked flags).size := by
  change 8 ≤ alignUp flags 4 + 4
  have aligned := alignUp_aligned flags (by decide : 0 < 4)
  have beyond : flags ≤ alignUp flags 4 := Nat.le_add_right _ _
  omega

theorem packed_saves_four {flags : Nat} (many : 5 ≤ flags) (fits : flags ≤ 8) :
    packed.size + 4 = (unpacked flags).size := by
  change 12 = alignUp flags 4 + 4
  have aligned := alignUp_aligned flags (by decide : 0 < 4)
  have below := padding_lt flags (by decide : 0 < 4)
  unfold alignUp at aligned ⊢
  omega

def unpackedBytes (value : Value flags) : List UInt8 :=
  List.ofFn (fun i : Fin flags => if value.bits.toNat.testBit i.val then 1 else 0) ++
    List.replicate (padding flags 4) 0 ++ List.ofFn value.payload

def packedFlagByte (value : Value flags) (fits : flags ≤ 8) : UInt8 :=
  UInt8.ofNatLT value.bits.toNat (BitVec.toNat_lt_twoPow_of_le fits)

def packedBytes (value : Value flags) (fits : flags ≤ 8) : List UInt8 :=
  List.ofFn value.payload ++ [packedFlagByte value fits, 0, 0, 0]

theorem unpacked_bytes_size (value : Value flags) :
    (unpackedBytes value).length = (unpacked flags).size := by
  simp [unpackedBytes, unpacked, alignUp, Nat.add_assoc]

theorem packed_bytes_size (value : Value flags) (fits : flags ≤ 8) :
    (packedBytes value fits).length = packed.size := by
  simp [packedBytes, packed]

theorem packed_flag (value : Value flags) (fits : flags ≤ 8) (i : Fin flags) :
    ((packedBytes value fits)[4]?).map (fun b => b.toNat.testBit i.val) =
      some (value.bits.toNat.testBit i.val) := by
  simp [packedBytes, packedFlagByte]

theorem unpacked_flag (value : Value flags) (i : Fin flags) :
    ((unpackedBytes value)[i.val]?).map (fun b => b == 1) =
      some (value.bits.toNat.testBit i.val) := by
  simp only [unpackedBytes, List.append_assoc]
  rw [List.getElem?_append_left (by simp), List.getElem?_ofFn]
  simp only [dite_eq_left i.isLt]
  cases value.bits.toNat.testBit i.val <;> decide

theorem packed_payload (value : Value flags) (fits : flags ≤ 8) (i : Fin 4) :
    (packedBytes value fits)[i.val]? = some (value.payload i) := by
  rw [packedBytes, List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt),
    List.getElem?_ofFn, dite_eq_left i.isLt]

theorem unpacked_payload (value : Value flags) (i : Fin 4) :
    (unpackedBytes value)[alignUp flags 4 + i.val]? = some (value.payload i) := by
  rw [unpackedBytes, List.getElem?_append_right]
  · simp only [List.length_append, List.length_ofFn, List.length_replicate, alignUp,
      Nat.add_sub_cancel_left, List.getElem?_ofFn, dite_eq_left i.isLt]
  · simp [alignUp]

/-- Both representations return the same logical field values. -/
theorem realignment_preserves_fields (value : Value flags) (fits : flags ≤ 8) :
    (∀ i : Fin flags, ((packedBytes value fits)[4]?).map (fun b => b.toNat.testBit i.val) =
      ((unpackedBytes value)[i.val]?).map (fun b => b == 1)) ∧
    (∀ i : Fin 4, (packedBytes value fits)[i.val]? =
      (unpackedBytes value)[alignUp flags 4 + i.val]?) :=
  ⟨fun i => (packed_flag value fits i).trans (unpacked_flag value i).symm,
    fun i => (packed_payload value fits i).trans (unpacked_payload value i).symm⟩

end Aethel.FlagRecordLayout

namespace Aethel.SingleFlagLayout

/-- Declaration order is u8, an aligned four-byte payload, u1, u8. -/
structure Value where
  first : UInt8
  payload : Fin 4 → UInt8
  flag : BitVec 1
  last : UInt8

def declarationOrder : RecordLayout :=
  ⟨12, 4, [⟨0, 1, 1⟩, ⟨4, 4, 4⟩, ⟨8, 1, 1⟩, ⟨9, 1, 1⟩]⟩

def alignmentOrder : RecordLayout :=
  ⟨8, 4, [⟨0, 4, 4⟩, ⟨4, 1, 1⟩, ⟨5, 1, 1⟩, ⟨6, 1, 1⟩]⟩

def declarationBytes (value : Value) : List UInt8 :=
  [value.first, 0, 0, 0] ++ List.ofFn value.payload ++ [value.flag.toNat.toUInt8, value.last, 0, 0]

def alignmentBytes (value : Value) : List UInt8 :=
  List.ofFn value.payload ++ [value.first, value.flag.toNat.toUInt8, value.last, 0]

theorem declarationOrder_valid : declarationOrder.Valid := by decide
theorem alignmentOrder_valid : alignmentOrder.Valid := by decide

/-- Reordering this record saves one alignment unit with an addressable u1.
Access through the layouts' offsets preserves each field and payload byte. -/
theorem single_u1_realignment (value : Value) :
    (alignmentBytes value).length = alignmentOrder.size ∧
    (declarationBytes value).length = declarationOrder.size ∧
    alignmentOrder.size + 4 = declarationOrder.size ∧
    (alignmentBytes value)[4]? = (declarationBytes value)[0]? ∧
    (alignmentBytes value)[5]? = (declarationBytes value)[8]? ∧
    (alignmentBytes value)[6]? = (declarationBytes value)[9]? ∧
    (∀ i : Fin 4, (alignmentBytes value)[i.val]? = (declarationBytes value)[4 + i.val]?) := by
  refine ⟨by simp [alignmentBytes, alignmentOrder], by simp [declarationBytes, declarationOrder],
    rfl, rfl, rfl, rfl, ?_⟩
  intro i
  have alternatives : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases alternatives with h | h | h | h <;> rw [h] <;> rfl

end Aethel.SingleFlagLayout
